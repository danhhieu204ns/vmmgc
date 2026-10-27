#!/usr/bin/env python3
"""Standalone best-effort downloader; Python 3.10+.

Install: python -m pip install yt-dlp==2026.8.19 requests Pillow
Run:     python download.py --limit 5 --workers 2
Parallel: --workers 4 --provider-workers 2 (bounded transfers per provider).
Retry:   python download.py --retry-failed
Pacing:  --delay sets the minimum interval between requests per provider.
Preview: python download.py --dry-run

Only this file and songs.jsonl are needed from the project. Output defaults to
rebuilt/ beside this script; existing dataset media is never read or overwritten.
Source URLs cannot guarantee byte-identical restoration; see rebuild_report.jsonl.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from copy import deepcopy
import hashlib
import hmac
import os
import math
import random
import threading
from email.utils import parsedate_to_datetime
from contextlib import contextmanager
import json
from pathlib import Path
import re
import sys
import time
from urllib.parse import urlparse, urlencode

ROOT = Path(__file__).resolve().parent
KINDS = ('audio', 'lyrics', 'cover')


def sha256(path):
    with path.open('rb') as stream:
        digest = hashlib.sha256()
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
        return digest.hexdigest()


def atomic(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(text, encoding='utf-8')
    temporary.replace(path)


def save_json(path, data):
    atomic(path, json.dumps(data, ensure_ascii=False, indent=2) + '\n')


def links(row):
    values = [s if isinstance(s, str) else s.get('url') for s in row.get('sources', [])]
    return list(dict.fromkeys(u for u in values if u))


def provider(url):
    parsed = urlparse(url)
    if parsed.scheme not in ('https', 'http'):
        return None
    if parsed.hostname in ('zingmp3.vn', 'www.zingmp3.vn'):
        return 'zing'
    if parsed.hostname in ('youtube.com', 'www.youtube.com', 'm.youtube.com', 'youtu.be'):
        return 'youtube'
    return None


def asset(path, out):
    return dict(path=path.relative_to(out).as_posix(), bytes=path.stat().st_size, sha256=sha256(path))


def valid_asset(item, out):
    path = out / item['path']
    return (path.resolve().is_relative_to(out.resolve()) and path.is_file()
            and not path.is_symlink() and path.stat().st_size == item['bytes']
            and sha256(path) == item['sha256'])


def zing_extractor_class():
    """Embedded adapter for the public Zing API; no project-local imports."""
    from yt_dlp.extractor.zingmp3 import ZingMp3IE
    from yt_dlp.utils import ExtractorError

    class ZingMp3CompatIE(ZingMp3IE):
        IE_NAME = "zingmp3:compat"
        API_VERSION = "1.20.4"
    
        def _api_url(self, url_type, params):
            api_slug = self._API_SLUGS[url_type]
            signed = {**params, "ctime": str(int(time.time())), "version": self.API_VERSION}
            digest = hashlib.sha256(
                "".join(f"{key}={value}" for key, value in sorted(signed.items())).encode()
            ).hexdigest()
            signature = hmac.new(
                b"acOrvUS15XRW2o9JksiK1KgQ6Vbds8ZW",
                (api_slug + digest).encode(), hashlib.sha512,
            ).hexdigest()
            query = {**signed, "apiKey": "X5BM3w8N7MKozC0B85o4KMlzLZKhV00y", "sig": signature}
            return f"{self._DOMAIN}{api_slug}?{urlencode(query)}"
    
        def _call_api(self, url_type, params, display_id=None, **kwargs):
            response = self._download_json(
                self._api_url(url_type, params), display_id or params.get("id"),
                note=f"Downloading {url_type} JSON metadata", **kwargs,
            )
            if response and response.get("err") not in (None, 0):
                if kwargs.get("fatal") is False:
                    return {}
                raise ExtractorError(
                    f"Zing API {url_type}: {response.get('msg', 'request failed')} "
                    f"(err={response['err']})", expected=True,
                )
            return (response or {}).get("data") or {}
    
        def _real_extract(self, url):
            song_id = self._match_id(url)
            response = self._request_webpage(
                url, song_id, note="Resolving song URL and anonymous session",
            )
            if not self._match_valid_url(response.url):
                raise ExtractorError("Zing redirected to a non-song page", expected=True)
            return super()._real_extract(response.url)
    return ZingMp3CompatIE


def http_status(exc):
    """Read wrapped HTTP errors without treating every access error as throttling."""
    seen = set()
    while exc is not None and id(exc) not in seen:
        seen.add(id(exc))
        response = getattr(exc, 'response', None)
        status = getattr(response, 'status_code', None) or getattr(exc, 'status', None) or getattr(exc, 'code', None)
        if isinstance(status, int):
            return status
        match = re.search(r'(?:HTTP Error |HTTP |status[=: ]+)([45]\d\d)\b', str(exc), re.I)
        if match:
            return int(match[1])
        exc = getattr(exc, 'cause', None) or exc.__cause__ or exc.__context__
    return None


def retry_after(response):
    value = getattr(response, 'headers', {}).get('Retry-After') if response is not None else None
    if not value:
        return None
    try:
        seconds = float(value)
        return max(0, seconds) if math.isfinite(seconds) else None
    except ValueError:
        try:
            return max(0, parsedate_to_datetime(value).timestamp() - time.time())
        except (ValueError, TypeError, OverflowError):
            return None


def error_retry_after(exc):
    """Find Retry-After on HTTP errors wrapped by an extractor/downloader."""
    seen = set()
    while exc is not None and id(exc) not in seen:
        seen.add(id(exc))
        response = getattr(exc, 'response', None)
        seconds = retry_after(response if response is not None else exc)
        if seconds is not None:
            return seconds
        exc = getattr(exc, 'cause', None) or getattr(exc, '__cause__', None) or getattr(exc, '__context__', None)
    return None


class RequestGate:
    """Shared provider pacing and cooldown; monotonic deadlines survive clock changes."""
    def __init__(self, interval, concurrency=2):
        self.interval = interval
        self.base_interval = interval
        self.successes = 0
        self.requests = 0
        self.rate_limits = 0
        self.next_request = 0.0
        self.blocked_until = 0.0
        self.lock = threading.Lock()
        self.source_lock = threading.BoundedSemaphore(concurrency)

    def wait(self):
        while True:
            with self.lock:
                now = time.monotonic()
                delay = max(self.next_request, self.blocked_until) - now
                if delay <= 0:
                    self.requests += 1
                    self.next_request = now + self.interval
                    return
            time.sleep(delay)

    def cooldown(self, seconds):
        with self.lock:
            self.blocked_until = max(self.blocked_until, time.monotonic() + seconds)
            self.interval = max(self.base_interval, min(30, max(self.interval * 2, 0.5)))
            self.successes = 0
            self.rate_limits += 1

    def success(self):
        with self.lock:
            self.successes += 1
            if self.successes >= 20:
                self.interval = max(self.base_interval, self.interval * 0.9)
                self.successes = 0


class DownloadRuntime:
    def __init__(self, args):
        self.gates = {kind: RequestGate(args.delay, args.provider_workers) for kind in ('zing', 'youtube')}
        self.local = threading.local()
        self.sessions = []
        self.lock = threading.Lock()

    def session(self):
        import requests
        if not hasattr(self.local, 'session'):
            self.local.session = requests.Session()
            with self.lock:
                self.sessions.append(self.local.session)
        return self.local.session

    def close(self):
        for session in self.sessions:
            session.close()


def backoff(attempt):
    return min(5 * 2 ** min(attempt, 6), 120) + random.uniform(0, 2)


class WebSource:
    """yt-dlp handles page extraction; requests downloads small image/lyric assets."""
    def __init__(self, url, directory, args):
        import yt_dlp
        self.url, self.directory, self.args = url, directory, args
        self.kind = provider(url)
        self.gate = args.runtime.gates[self.kind]
        self.session = args.runtime.session()
        options = dict(quiet=True, no_warnings=True, noprogress=True, noplaylist=True,
                       socket_timeout=args.timeout, retries=args.retries,
                       extractor_retries=args.retries, fragment_retries=args.retries,
                       format='bestaudio', ignore_no_formats_error=True,
                       concurrent_fragment_downloads=1,
                       retry_sleep_functions={k: backoff for k in ('http', 'fragment', 'extractor')},
                       outtmpl=str(directory / 'audio.%(ext)s'))
        if args.cookies:
            options['cookiefile'] = str(args.cookies)
        gate = self.gate

        class PacedYoutubeDL(yt_dlp.YoutubeDL):
            def urlopen(self, request):
                gate.wait()
                try:
                    response = super().urlopen(request)
                    gate.success()
                    return response
                except Exception as exc:
                    status = http_status(exc)
                    seconds = error_retry_after(exc)
                    if status == 429 or (status == 503 and seconds is not None):
                        gate.cooldown(seconds if seconds is not None else backoff(0))
                    raise

        self.ydl = PacedYoutubeDL(options)
        self.ie_key = None
        if self.kind == 'zing':
            ZingMp3CompatIE = zing_extractor_class()
            self.ydl.add_info_extractor(ZingMp3CompatIE(self.ydl))
            self.ie_key = ZingMp3CompatIE.ie_key()
        self.info = None

    def __enter__(self):
        try:
            self.info = self.ydl.extract_info(self.url, download=False, ie_key=self.ie_key)
            if not self.info or self.info.get('_type') in ('playlist', 'multi_video'):
                raise ValueError('Source must identify one song/video')
            return self
        except BaseException:
            self.ydl.close()
            raise

    def __exit__(self, *unused):
        self.ydl.close()

    def audio(self):
        if not self.info.get('formats'):
            raise ValueError('No accessible audio format')
        info = self.ydl.process_ie_result(deepcopy(self.info), download=True)
        candidates = [Path(d['filepath']) for d in info.get('requested_downloads', []) if d.get('filepath')]
        candidates.append(Path(self.ydl.prepare_filename(info)))
        for path in candidates:
            if path.is_file() and path.stat().st_size:
                return path
        raise ValueError('Downloader did not produce an audio file')

    def fetch(self, url, name):
        import requests
        path = self.directory / name
        for attempt in range(self.args.retries + 1):
            try:
                self.gate.wait()
                with self.session.get(url, timeout=(10, self.args.timeout), stream=True) as response:
                    seconds = retry_after(response)
                    if response.status_code == 429 or (response.status_code == 503 and seconds is not None):
                        self.gate.cooldown(seconds if seconds is not None else backoff(attempt))
                    response.raise_for_status()
                    with path.open('wb') as stream:
                        size = 0
                        for chunk in response.iter_content(65536):
                            size += len(chunk)
                            if size > 25 * 1024 * 1024:
                                raise ValueError('Image/lyric response exceeds 25 MiB')
                            stream.write(chunk)
                if not path.stat().st_size:
                    raise ValueError('Empty response')
                self.gate.success()
                return path
            except Exception as exc:
                path.unlink(missing_ok=True)
                status = http_status(exc)
                transient = isinstance(exc, (requests.Timeout, requests.ConnectionError)) or status in (408, 429, 500, 502, 503, 504)
                if attempt == self.args.retries or not transient:
                    raise
                # Cooldown is shared with other workers; wait once at the next
                # gate admission instead of sleeping again in this worker.
                if status != 429 and not (status == 503 and error_retry_after(exc) is not None):
                    time.sleep(backoff(attempt))

    def cover(self):
        from PIL import Image
        url = self.info.get('thumbnail')
        if not url:
            raise ValueError('No cover/thumbnail URL')
        path = self.fetch(url, 'cover.download')
        with Image.open(path) as image:
            ext = {'JPEG': '.jpg', 'PNG': '.png', 'WEBP': '.webp', 'GIF': '.gif'}.get(image.format)
            image.verify()
        if not ext:
            raise ValueError('Unsupported image format')
        target = path.with_suffix(ext)
        path.replace(target)
        return target

    def lyrics(self):
        # YouTube captions (especially automatic captions) are not song lyrics.
        if self.kind != 'zing':
            raise ValueError('No supported lyric source; YouTube captions are not treated as lyrics')
        subtitles = self.info.get('subtitles') or {}
        choices = subtitles.get('origin') or []
        url = next((s['url'] for s in choices if s.get('url')), None)
        if not url:
            raise ValueError('No source lyrics available')
        path = self.fetch(url, 'lyrics.lrc')
        text = path.read_text(encoding='utf-8-sig')
        if not text.strip() or re.search(r'<(?:!doctype|html|body)\b', text, re.I):
            raise ValueError('Invalid lyric response')
        return path


def rebuild_record(original, out, args, previous=None, backend=WebSource):
    row = deepcopy(original)
    row.pop('split', None)
    row['sources'] = links(original)
    row['assets'] = {kind: [] for kind in KINDS}
    events = []
    wanted = {kind for kind in KINDS if original.get('assets', {}).get(kind)}
    if original.get('lyrics'):
        wanted.add('lyrics')
    if previous:
        for kind in KINDS:
            row['assets'][kind] = [a for a in previous['row']['assets'][kind] if valid_asset(a, out)]
    rid = row['record_id']
    if original.get('lyrics') and not row['assets']['lyrics']:
        path = out / 'lyrics' / f'{rid}_inline.txt'
        # Exact UTF-8 text from the manifest, without adding a newline.
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(original['lyrics'].encode('utf-8'))
        row['assets']['lyrics'] = [asset(path, out)]
    pending = wanted - {kind for kind in KINDS if row['assets'][kind]}
    for index, url in enumerate(row['sources']):
        if not pending:
            break
        if not provider(url):
            events.append(dict(url=url, error='Unsupported source URL'))
            continue
        if provider(url) == 'youtube' and pending == {'lyrics'}:
            events.append(dict(url=url, kind='lyrics', error='YouTube does not supply supported lyrics; extraction skipped'))
            continue
        work = out / '.work' / rid / str(index)
        work.mkdir(parents=True, exist_ok=True)
        started = time.monotonic()
        gate = args.runtime.gates[provider(url)]
        try:
            # Bound active transfers while pacing every request across workers.
            with gate.source_lock, backend(url, work, args) as source:
                for kind in KINDS:
                    if kind not in pending:
                        continue
                    try:
                        asset_started = time.monotonic()
                        downloaded = getattr(source, kind)()
                        target = out / kind / f'{rid}{downloaded.suffix}'
                        target.parent.mkdir(parents=True, exist_ok=True)
                        downloaded.replace(target)
                        row['assets'][kind] = [asset(target, out)]
                        pending.remove(kind)
                        events.append(dict(url=url, kind=kind, status='downloaded', seconds=round(time.monotonic() - asset_started, 3)))
                    except Exception as exc:
                        events.append(dict(url=url, kind=kind, error=str(exc), http_status=http_status(exc)))
        except Exception as exc:
            events.append(dict(url=url, error=str(exc), http_status=http_status(exc)))
        finally:
            events.append(dict(url=url, status='source_finished', seconds=round(time.monotonic() - started, 3)))
    comparison = {}
    for kind in KINDS:
        expected = original.get('assets', {}).get(kind, [])
        actual_hashes = {a['sha256'] for a in row['assets'][kind]}
        known = {a['sha256'] for a in expected if a.get('sha256')}
        comparison[kind] = dict(expected_files=len(expected), actual_files=len(row['assets'][kind]),
                                matched_original_hashes=len(known & actual_hashes),
                                missing_original_hashes=sorted(known - actual_hashes),
                                new_hashes=sorted(actual_hashes - known))
    exact = all(
        len(original.get('assets', {}).get(k, [])) == len(row['assets'][k])
        and all(a.get('sha256') for a in original.get('assets', {}).get(k, []))
        and sorted(a['sha256'] for a in original.get('assets', {}).get(k, []))
        == sorted(a['sha256'] for a in row['assets'][k]) for k in KINDS)
    report = dict(record_id=rid, status='partial' if pending else 'available',
                  missing_kinds=sorted(pending), byte_identical_assets=exact,
                  comparison=comparison, events=events)
    return dict(row=row, report=report)


def export(out, records):
    rows = [r['row'] for r in records]
    for row in rows:
        save_json(out / 'metadata' / f"{row['record_id']}.json", row)
    atomic(out / 'songs.jsonl', ''.join(json.dumps(r, ensure_ascii=False)+'\n' for r in rows))
    atomic(out / 'rebuild_report.jsonl', ''.join(json.dumps(r['report'], ensure_ascii=False)+'\n' for r in records))
    stats = dict(records=len(rows), statuses=dict(Counter(r['report']['status'] for r in records)),
                 byte_identical_records=sum(r['report']['byte_identical_assets'] for r in records),
                 **{'with_'+k: sum(bool(r['assets'][k]) for r in rows) for k in KINDS})
    save_json(out / 'stats.json', stats)
    checks = {a['path']: a['sha256'] for r in rows for aa in r['assets'].values() for a in aa}
    names = [f"metadata/{r['record_id']}.json" for r in rows] + ['songs.jsonl', 'stats.json', 'rebuild_report.jsonl']
    checks.update({name: sha256(out/name) for name in names})
    atomic(out / 'SHA256SUMS', ''.join(f'{sha}  {name}\n' for name, sha in sorted(checks.items())))
    return stats


@contextmanager
def output_lock(path):
    """OS lock released even after a crash, on Windows and POSIX."""
    with path.open('a+b') as stream:
        if os.name == 'nt':
            import msvcrt
            stream.seek(0, os.SEEK_END)
            if stream.tell() == 0:
                stream.write(b'0')
                stream.flush()
            stream.seek(0)
            try:
                msvcrt.locking(stream.fileno(), msvcrt.LK_NBLCK, 1)
            except OSError as exc:
                raise SystemExit('Another rebuild is running in this output directory') from exc
            try:
                yield
            finally:
                stream.seek(0)
                msvcrt.locking(stream.fileno(), msvcrt.LK_UNLCK, 1)
        else:
            import fcntl
            try:
                fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as exc:
                raise SystemExit('Another rebuild is running in this output directory') from exc
            try:
                yield
            finally:
                fcntl.flock(stream, fcntl.LOCK_UN)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=ROOT/'songs.jsonl')
    parser.add_argument('--output', type=Path, default=ROOT/'rebuilt')
    parser.add_argument('--limit', type=int, help='Process first N selected rows; omit for all')
    parser.add_argument('--record-id', action='append', help='Select record ID; repeatable')
    parser.add_argument('--delay', type=float, default=1.0, help='Minimum seconds between requests per provider (including media)')
    parser.add_argument('--workers', type=int, default=4, help='Concurrent records (default: 4)')
    parser.add_argument('--provider-workers', type=int, default=2, help='Maximum active sources per provider (default: 2; use 1 for serial downloads)')
    parser.add_argument('--timeout', type=int, default=30)
    parser.add_argument('--retries', type=int, default=2)
    parser.add_argument('--cookies', type=Path, help='Optional yt-dlp Netscape cookie file')
    parser.add_argument('--retry-failed', action='store_true', help='Retry saved records with missing asset types')
    parser.add_argument('--dry-run', action='store_true', help='Validate manifest and show plan, without writes/network')
    args = parser.parse_args()
    if args.workers < 1 or args.provider_workers < 1 or not math.isfinite(args.delay) or args.delay < 0 or args.timeout < 1 or args.retries < 0 or (args.limit is not None and args.limit < 1):
        parser.error('Invalid workers, provider-workers, delay, timeout, retries or limit')
    manifest, out = args.manifest.resolve(), args.output.resolve()
    if manifest.is_relative_to(out):
        parser.error('Output must be separate from the input dataset')
    raw = manifest.read_bytes()
    rows = [json.loads(line) for line in raw.splitlines() if line.strip()]
    ids = [r['record_id'] for r in rows]
    if len(set(ids)) != len(ids) or not all(re.fullmatch(r'[A-Za-z0-9_-]+', rid) for rid in ids):
        parser.error('Duplicate or unsafe record IDs')
    if args.record_id:
        if set(args.record_id) - set(ids):
            parser.error('Unknown record ID')
        rows = [r for r in rows if r['record_id'] in args.record_id]
    if args.limit:
        rows = rows[:args.limit]
    if args.dry_run:
        print(json.dumps(dict(records=len(rows), sources=dict(Counter(provider(u) or 'unsupported' for r in rows for u in links(r))),
                              expected_files={k: sum(len(r.get('assets', {}).get(k, [])) for r in rows) for k in KINDS}), indent=2))
        return
    try:
        import yt_dlp
        import requests
        from PIL import Image
    except ImportError as exc:
        parser.error(f'{exc}. Install: python -m pip install yt-dlp==2026.8.19 requests Pillow')
    config = dict(manifest_sha256=hashlib.sha256(raw).hexdigest(), schema_version=1)
    marker = out / 'rebuild_config.json'
    if out.exists() and any(out.iterdir()):
        if not marker.is_file() or json.loads(marker.read_text(encoding='utf-8')) != config:
            parser.error('Output is not a rebuild of this exact manifest; choose an empty directory')
    out.mkdir(parents=True, exist_ok=True)
    # Exclusive run lock prevents two processes from modifying the same output.
    with output_lock(out / '.lock'):
        save_json(marker, config)
        interrupted = False
        args.runtime = DownloadRuntime(args)

        def process(row):
            checkpoint = out / '.state' / f"{row['record_id']}.json"
            previous = json.loads(checkpoint.read_text(encoding='utf-8')) if checkpoint.exists() else None
            valid = previous and all(valid_asset(a, out) for aa in previous['row']['assets'].values() for a in aa)
            retry = previous and args.retry_failed and previous['report']['status'] == 'partial'
            if not valid or retry:
                result = rebuild_record(row, out, args, previous)
                save_json(checkpoint, result)
            else:
                result = previous
            return row['record_id'], result['report']['status']

        pool = ThreadPoolExecutor(max_workers=args.workers)
        futures = []
        try:
            # Mix primary providers so a long Zing prefix does not starve YouTube.
            groups = {}
            for row in rows:
                primary = next((provider(u) for u in links(row) if provider(u)), 'local')
                groups.setdefault(primary, deque()).append(row)
            ordered = []
            while any(groups.values()):
                for group in groups.values():
                    if group:
                        ordered.append(group.popleft())
            futures = [pool.submit(process, row) for row in ordered]
            for index, future in enumerate(as_completed(futures), 1):
                rid, status = future.result()
                print(f"[{index}/{len(rows)}] {rid}: {status}", flush=True)
        except KeyboardInterrupt:
            interrupted = True
            for future in futures:
                future.cancel()
            print('Interrupted; waiting for active downloads to save checkpoints.', file=sys.stderr)
        finally:
            pool.shutdown(wait=True, cancel_futures=True)
            args.runtime.close()
            print(json.dumps({'network': {
                kind: dict(requests=gate.requests, rate_limits=gate.rate_limits,
                           request_interval=round(gate.interval, 3))
                for kind, gate in args.runtime.gates.items()
            }}, ensure_ascii=False), flush=True)
        # Export all completed checkpoints in source order, including previous invocations.
        records = []
        for row in (json.loads(line) for line in raw.splitlines() if line.strip()):
            checkpoint = out / '.state' / f"{row['record_id']}.json"
            if checkpoint.exists():
                records.append(json.loads(checkpoint.read_text(encoding='utf-8')))
        print(json.dumps(export(out, records), ensure_ascii=False, indent=2))
        if interrupted:
            raise SystemExit(130)


if __name__ == '__main__':
    main()
