#!/usr/bin/env python3
"""
Twitch VOD archive. Runs on GitHub Actions, not on anyone's machine.

Every few hours: list this channel's Twitch VODs, skip anything already
archived or still being written, download it, upload it to YouTube as private,
record it in the manifest, and post a card to a private Discord.

Notes that matter:

* Quota. videos.insert used to cost 1600 units against a 10,000/day budget,
  which capped you at six uploads a day. Google cut it to 1 unit with a
  100/day allowance. The old Forge script capped itself at 5 per run because
  of the old maths; that cap is gone. The real limits now are runner disk and
  the six hour job timeout, so we bound by BYTES and TIME, not by count.

* Unfinished VODs. A stream that is still live, or finished in the last few
  minutes, has a VOD that Twitch is still writing. Downloading it gets you a
  truncated file that looks complete. We skip anything younger than 20 min.

* Disk. A runner has ~36 GB free after cleanup. Twitch VODs from this channel
  are single-rendition 1080p60 source (~3.1 GB/hour), so anything over ~10 hours
  cannot be held in one file. Oversized VODs are downloaded and uploaded in
  time slices ("Part 1/2"), planned BEFORE the download starts, and every
  scratch file is wiped between VODs. See the DISK HANDLING note below.

* Private means private. Only the uploading account can ever watch these.
  That is deliberate. The Discord card carries the metadata so the other
  person can see what exists without being able to open it.
"""

import json
import math
import os
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone, timedelta

import requests
from google.oauth2.credentials import Credentials
from googleapiclient.discovery import build
from googleapiclient.http import MediaFileUpload
try:
    from googleapiclient.errors import HttpError
except ImportError:  # keeps the module importable where the client library is stubbed
    class HttpError(Exception):
        pass

HERE = os.path.dirname(os.path.abspath(__file__))
MANIFEST = os.path.join(HERE, "uploaded.json")

TWITCH_ID = os.environ["TWITCH_CLIENT_ID"]
TWITCH_SECRET = os.environ["TWITCH_CLIENT_SECRET"]
TWITCH_CHANNEL = os.environ["TWITCH_CHANNEL"]
YT_ID = os.environ["YT_CLIENT_ID"]
YT_SECRET = os.environ["YT_CLIENT_SECRET"]
YT_REFRESH = os.environ["YT_REFRESH_TOKEN"]
WHO = os.environ.get("ARCHIVE_LANE", TWITCH_CHANNEL)
WORKER = os.environ.get("NOTIFY_WORKER_URL", "").rstrip("/")
WORKER_TOKEN = os.environ.get("NOTIFY_WEBHOOK_TOKEN", "")

# Stay inside the runner's disk and the 6h job limit.
# Bytes are no longer a disk guard (each file is deleted after upload); the real
# budgets are time and per-VOD disk planning. Kept as a very high backstop.
MAX_BYTES_PER_RUN = int(os.environ.get("MAX_BYTES_PER_RUN", 400 * 1024**3))
# 4.5h, not 5h: the job limit is 6h and one slice (download + upload) can take ~1h.
DEADLINE = time.time() + int(os.environ.get("RUN_SECONDS", int(4.5 * 3600)))
MIN_AGE_MINUTES = 20
T0 = time.time()
# GitHub kills the job at timeout-minutes (350). Nothing may be STARTED that could not
# plausibly finish before this, measured from process start.
JOB_LIMIT_S = int(5.5 * 3600)
# YouTube rejects uploads longer than 12 hours, whatever the runner's disk allows.
MAX_PART_SECONDS = 10 * 3600

# ------------------------------------------------------------- DISK HANDLING
# History: from 2026-09-08 every run died with "[Errno 28] No space left on
# device" and archived NOTHING for two weeks, burning ~1,300 Actions minutes
# (the whole monthly allowance) while eight streams aged towards Twitch's ~14
# day deletion. The cause was one 12h44m stream (37 GB; Twitch stored ONLY the
# 1080p60 source rendition, so there is no smaller format to fall back to). It
# sorted first because the queue is oldest-first, it can never fit on a ~36 GB
# runner, and its debris was never deleted: os.remove(path) misses "path.part",
# so the seven VODs queued behind it failed instantly too, including small ones.
#
# Three rules follow. Wipe by PREFIX, never by one filename. Estimate size
# BEFORE downloading, so a doomed VOD fails in seconds rather than after two
# hours. And cut a VOD that cannot fit into time slices.
DISK_SAFETY = 3 * 1024**3
# Native download = ONE file (yt-dlp appends fragments to a .part, then renames it) because
# download() passes --fixup never. Without that flag, and with ffmpeg installed, yt-dlp
# makes a second full-size remuxed copy (2x). The old, proven behaviour (no ffmpeg on the
# runner) stored an MPEG-TS stream under the .mp4 name and YouTube ingested all 33 archives.
NATIVE_FACTOR = 1.1
SLICE_FACTOR = 1.15   # ffmpeg slice mode writes the final mp4 directly: ~1x plus mux overhead
# ~8.8 Mbps. Deliberately pessimistic: an over-estimate only costs an extra slice.
FALLBACK_BYTES_PER_SEC = 1_100_000


def log(msg):
    print(msg, flush=True)


def load_manifest():
    if not os.path.exists(MANIFEST):
        return []
    with open(MANIFEST) as fh:
        try:
            return json.load(fh)
        except json.JSONDecodeError as exc:
            # Do NOT return []. An empty manifest makes every archived VOD still on
            # Twitch look unarchived and re-uploads all of them (~700 GB).
            sys.exit(f"uploaded.json is corrupt ({exc}); refusing to run rather than re-upload everything")


def save_manifest(done):
    # Atomic: a kill or a full disk mid-write must never leave a truncated file.
    tmp = MANIFEST + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(done, fh, indent=1)
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, MANIFEST)


def checkpoint_manifest():
    """Push uploaded.json NOW. Runs last for hours; if the job is killed (timeout,
    cancellation, runner loss) after several uploads, the workflow's end-of-job commit
    step is the only thing that would record them, and it may not run. An unrecorded
    upload is re-done next time: a duplicate on YouTube and another hour of minutes."""
    if os.environ.get("GITHUB_ACTIONS") != "true":
        return

    def git(*a):
        return subprocess.run(["git", *a], cwd=HERE, capture_output=True, text=True, timeout=120)

    try:
        git("config", "user.name", "vod-archiver-bot")
        git("config", "user.email", "vod-archiver-bot@users.noreply.github.com")
        git("add", "uploaded.json")
        if git("diff", "--cached", "--quiet").returncode == 0:
            return
        git("commit", "-m", f"archive: {datetime.now(timezone.utc):%Y-%m-%dT%H:%MZ}")
        git("pull", "--rebase", "-q", "origin", "main")
        res = git("push", "-q", "origin", "HEAD:main")
        if res.returncode != 0:
            log(f"  manifest checkpoint push failed (the end-of-job step will retry): {res.stderr[-200:]}")
    except Exception as exc:  # noqa: BLE001 - a checkpoint must never fail the archive
        log(f"  manifest checkpoint skipped: {exc}")


def twitch_token():
    r = requests.post("https://id.twitch.tv/oauth2/token", params={
        "client_id": TWITCH_ID, "client_secret": TWITCH_SECRET,
        "grant_type": "client_credentials"}, timeout=30)
    r.raise_for_status()
    return r.json()["access_token"]


def twitch_vods(token):
    h = {"Client-ID": TWITCH_ID, "Authorization": f"Bearer {token}"}
    u = requests.get("https://api.twitch.tv/helix/users",
                     params={"login": TWITCH_CHANNEL}, headers=h, timeout=30)
    u.raise_for_status()
    users = u.json().get("data", [])
    if not users:
        sys.exit(f"Twitch channel '{TWITCH_CHANNEL}' not found")
    uid = users[0]["id"]

    out, cursor = [], None
    while True:
        params = {"user_id": uid, "type": "archive", "first": 100}
        if cursor:
            params["after"] = cursor
        r = requests.get("https://api.twitch.tv/helix/videos",
                         params=params, headers=h, timeout=30)
        r.raise_for_status()
        body = r.json()
        out.extend(body.get("data", []))
        cursor = body.get("pagination", {}).get("cursor")
        if not cursor:
            return out


def parse_duration(s):
    """Twitch gives '3h21m9s'. Return seconds."""
    total, num = 0, ""
    for ch in s:
        if ch.isdigit():
            num += ch
        else:
            total += int(num or 0) * {"h": 3600, "m": 60, "s": 1}.get(ch, 0)
            num = ""
    return total


def youtube():
    creds = Credentials(
        None, refresh_token=YT_REFRESH, client_id=YT_ID, client_secret=YT_SECRET,
        token_uri="https://oauth2.googleapis.com/token",
    )
    return build("youtube", "v3", credentials=creds, cache_discovery=False)


PLAYLIST_TITLE = "VoD Archive"


def get_or_create_playlist(yt):
    """Find the archive playlist, or make it. Returns its id, or None if the
    token predates the playlist scope - in which case uploads still work and
    only the playlist step is skipped."""
    try:
        req = yt.playlists().list(part="snippet", mine=True, maxResults=50)
        while req is not None:
            res = req.execute()
            for p in res.get("items", []):
                if p["snippet"]["title"].strip().lower() == PLAYLIST_TITLE.lower():
                    log(f"using existing playlist '{PLAYLIST_TITLE}' ({p['id']})")
                    return p["id"]
            req = yt.playlists().list_next(req, res)

        created = yt.playlists().insert(
            part="snippet,status",
            body={
                "snippet": {
                    "title": PLAYLIST_TITLE,
                    "description": "Twitch VODs archived automatically before Twitch deletes them.",
                },
                # Private, to match the videos. A public playlist of private
                # videos would show as a wall of unavailable entries anyway.
                "status": {"privacyStatus": "private"},
            },
        ).execute()
        log(f"created playlist '{PLAYLIST_TITLE}' ({created['id']})")
        return created["id"]
    except Exception as exc:  # noqa: BLE001
        log(f"playlist unavailable ({exc}) - uploads will still work, just not grouped")
        return None


def add_to_playlist(yt, playlist_id, video_id):
    if not playlist_id:
        return False
    try:
        yt.playlistItems().insert(
            part="snippet",
            body={"snippet": {
                "playlistId": playlist_id,
                "resourceId": {"kind": "youtube#video", "videoId": video_id},
            }},
        ).execute()
        return True
    except Exception as exc:  # noqa: BLE001 - a playlist failure must not fail the archive
        log(f"  could not add to playlist: {exc}")
        return False


def free_bytes():
    return shutil.disk_usage(HERE).free


def wipe_temp():
    """Delete every scratch file. Matches the PREFIX on purpose: yt-dlp leaves
    x.mp4.part, x.mp4.ytdl and x.temp.mp4 beside the target, and deleting only
    the target is exactly what filled the disk for two weeks."""
    removed = 0
    for name in os.listdir(HERE):
        if not name.startswith("_tmp_"):
            continue
        p = os.path.join(HERE, name)
        try:
            shutil.rmtree(p) if os.path.isdir(p) else os.remove(p)
            removed += 1
        except OSError as exc:
            log(f"  could not remove {name}: {exc}")
    return removed


def probe_rate(vod):
    """Bytes per second of the best rendition, from yt-dlp's metadata (one
    request, nothing downloaded). Falls back to a pessimistic constant."""
    try:
        res = subprocess.run(
            ["yt-dlp", "-J", "--no-warnings", "--skip-download", vod["url"]],
            capture_output=True, text=True, timeout=120)
        info = json.loads(res.stdout)
        best = 0.0
        for f in info.get("formats", []):
            if f.get("vcodec") not in (None, "none") and f.get("tbr"):
                best = max(best, float(f["tbr"]))
        if best:
            return (best + 350) * 1000 / 8   # +350 kbps: the audio-only rendition, as a margin
    except Exception as exc:  # noqa: BLE001 - a failed probe must not stop the archive
        log(f"  size probe failed ({exc}); assuming {FALLBACK_BYTES_PER_SEC / 1e6:.1f} MB/s")
    return FALLBACK_BYTES_PER_SEC


class QuotaStop(Exception):
    """YouTube says stop for today (API quota or daily upload limit). Retrying is pointless."""


def est_seconds(nbytes):
    """Deliberately pessimistic wall time to download and then upload nbytes."""
    return nbytes / 5e6 + nbytes / 15e6 + 300


def would_overrun(nbytes):
    return time.time() + est_seconds(nbytes) > T0 + JOB_LIMIT_S


def plan_slices(duration_s, rate, free):
    """None = download the whole VOD the normal way. Otherwise a list of
    (start_s, end_s) slices, each sized to fit the free disk AND YouTube's 12h cap."""
    room = free - DISK_SAFETY
    if room < 2 * 1024**3:
        raise RuntimeError(f"only {free / 1e9:.1f} GB free after the safety margin")
    if duration_s <= MAX_PART_SECONDS and duration_s * rate * NATIVE_FACTOR <= room:
        return None
    per = min(int(room / SLICE_FACTOR / rate), MAX_PART_SECONDS)
    # A multiple of 60 keeps the rounded-up slice length below `per`: rounding a slice UP
    # to a whole minute past `per` made the per-slice fit check refuse it forever.
    per = max(600, (per // 60) * 60)
    parts = math.ceil(duration_s / per)
    chunk = math.ceil(duration_s / parts / 60) * 60           # equal slices, whole minutes
    return [(i * chunk, min(duration_s, (i + 1) * chunk))
            for i in range(parts) if i * chunk < duration_s]


def media_playlist_url(vod):
    """The media playlist of the rendition `-f best` downloads (one request, nothing downloaded)."""
    res = subprocess.run(["yt-dlp", "-f", "best", "-g", "--no-warnings", vod["url"]],
                         capture_output=True, text=True, timeout=120)
    urls = [u for u in res.stdout.split() if u.startswith("http")]
    if res.returncode != 0 or not urls:
        raise RuntimeError(f"yt-dlp gave no playlist URL: {res.stderr[-300:]}")
    return urls[0]


def write_slice_playlist(url, start, end, out_path):
    """Write a local m3u8 listing only the segments that overlap [start, end), with absolute
    URLs. Returns the seconds it covers (what the finished file should measure), or None."""
    res = requests.get(url, timeout=60)
    res.raise_for_status()
    base = url.split("?", 1)[0].rsplit("/", 1)[0] + "/"
    target, picked, t, extinf = "10", [], 0.0, None
    for line in res.text.splitlines():
        line = line.strip()
        if line.startswith("#EXT-X-TARGETDURATION:"):
            target = line.split(":", 1)[1]
        elif line.startswith("#EXTINF:"):
            extinf = float(line[8:].split(",", 1)[0])
        elif line and not line.startswith("#") and extinf is not None:
            # Overlap, not containment: the segment straddling a cut goes in BOTH slices, so
            # neighbouring parts share a few seconds instead of losing them.
            if t + extinf > start and t < end:
                picked.append((extinf, line if "://" in line else base + line))
            t += extinf
            extinf = None
    if not picked:
        return None
    with open(out_path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(f"#EXTM3U\n#EXT-X-VERSION:3\n#EXT-X-TARGETDURATION:{target}\n"
                 "#EXT-X-PLAYLIST-TYPE:VOD\n#EXT-X-MEDIA-SEQUENCE:0\n")
        for d, u in picked:
            fh.write(f"#EXTINF:{d:.3f},\n{u}\n")
        fh.write("#EXT-X-ENDLIST\n")
    return sum(d for d, _ in picked)


def download_slice(vod, path, start, end, timeout):
    """One time slice, written straight to mp4 by ffmpeg. Returns the seconds it should
    measure, or False.

    NEVER seek with -ss (which is what yt-dlp --download-sections does). MPEG-TS timestamps
    are 33 bits at 90 kHz, so they WRAP back to zero every 26h30m. ffmpeg's HLS seek picks
    the right segment, then throws packets away until one is stamped at or after the target.
    Past the wrap no packet ever is: it read the whole rest of the VOD, wrote nothing,
    exited 0, and every run failed the length check on the same slice. Found 2026-10-02 on a
    48h stream whose Parts 4 and 5 (both after the wrap) could never be archived. Handing
    ffmpeg a playlist of just this slice's segments means there is no seek at all, and its
    normal wrap correction (relative to the first packet) handles a slice that crosses one.
    """
    m3u8 = path + ".m3u8"   # _tmp_ prefix, so wipe_temp() removes it with the rest
    try:
        covered = write_slice_playlist(media_playlist_url(vod), start, end, m3u8)
    except Exception as exc:  # noqa: BLE001
        log(f"  could not build the slice playlist: {exc}")
        return False
    if not covered:
        log("  the slice holds no segments; not downloading")
        return False
    # ffmpeg's HLS reader does NOT retry a failed segment by default, so one transient CDN
    # error silently drops a few seconds while the file still reports the right duration
    # (fault-injection test: a single 500 lost a segment). The retries fix that case, and
    # the read timeout stops a stalled connection hanging the job until it is killed. A
    # segment that keeps failing is skipped, and biggest_gap() then catches the hole.
    cmd = ["ffmpeg", "-hide_banner", "-nostdin", "-loglevel", "error", "-y",
           "-protocol_whitelist", "file,http,https,tcp,tls,crypto",
           "-seg_max_retry", "10", "-rw_timeout", "60000000",
           "-i", m3u8,
           "-map", "0:v:0", "-map", "0:a:0?", "-c", "copy", "-bsf:a", "aac_adtstoasc",
           "-f", "mp4", path]
    try:
        res = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        log(f"  ffmpeg still running after {timeout}s; stopped it")
        return False
    if res.returncode != 0:
        log(f"  ffmpeg failed: {res.stderr[-400:]}")
        return False
    return covered if os.path.exists(path) else False


def download(vod, path, start=None, end=None, expect_bytes=None):
    """True (whole VOD) or the slice's expected seconds when it worked; False when not."""
    timeout = int(est_seconds(expect_bytes)) if expect_bytes else None
    if start is not None:
        return download_slice(vod, path, start, end, timeout)
    cmd = ["yt-dlp", "-f", "best", "--no-progress", "--no-warnings",
           "--fixup", "never",   # see NATIVE_FACTOR: one file on disk, not two
           "-o", path, vod["url"]]
    try:
        res = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        log(f"  yt-dlp still running after {timeout}s; stopped it")
        return False
    if res.returncode != 0:
        log(f"  yt-dlp failed: {res.stderr[-400:]}")
        return False
    return os.path.exists(path)


def probe_seconds(path):
    """Seconds, or None if ffprobe ran but could not read the file. Raises
    FileNotFoundError if ffprobe itself is not installed."""
    out = subprocess.run(
        ["ffprobe", "-v", "error", "-show_entries", "format=duration",
         "-of", "default=nw=1:nk=1", path],
        capture_output=True, text=True, timeout=120).stdout.strip()
    try:
        return float(out)
    except ValueError:
        return None


def looks_complete(path, expected_s, min_bytes=0):
    """A truncated download looks exactly like a finished one. Compare length and size."""
    # A slice starting past the real end makes yt-dlp print "Download completed" while
    # ffmpeg says "Output file is empty, nothing was encoded". An empty or unreadable
    # file must NEVER pass. Only a missing ffprobe binary fails open.
    if not os.path.exists(path) or os.path.getsize(path) == 0:
        log("  LENGTH CHECK FAILED: the downloaded file is empty. Not uploading.")
        return False
    if min_bytes and os.path.getsize(path) < min_bytes:
        log(f"  SIZE CHECK FAILED: {os.path.getsize(path) / 1e9:.2f} GB is under the "
            f"{min_bytes / 1e9:.2f} GB floor for this length. Not uploading.")
        return False
    try:
        got = probe_seconds(path)
    except FileNotFoundError:
        log("  ffprobe is not installed; length cannot be checked, continuing")
        return True
    if got is None:
        log("  LENGTH CHECK FAILED: ffprobe cannot read the file (corrupt?). Not uploading.")
        return False
    tol = max(20.0, 0.001 * expected_s)   # measured: real slices land within ~2s of the request
    if abs(got - expected_s) > tol:
        log(f"  LENGTH CHECK FAILED: file is {got:.0f}s, expected {expected_s:.0f}s "
            f"(+/-{tol:.0f}s). Not uploading.")
        return False
    return True


def biggest_gap(path):
    """Largest jump between consecutive VIDEO packet timestamps, in seconds. None if it
    cannot be measured. Slice mode (ffmpeg) exits 0 and reports the right duration even
    after dropping a segment on a mid-transfer connection reset; the only trace is a hole
    in the timestamps (fault-injection test: a 4 s hole). Frames are ~0.017s apart, so
    anything over about a second is missing footage."""
    try:
        out = subprocess.run(
            ["ffprobe", "-v", "error", "-select_streams", "v:0",
             "-show_entries", "packet=pts_time", "-of", "csv=p=0", path],
            capture_output=True, text=True, timeout=1800).stdout
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return None
    ts = []
    for tok in out.split():
        try:
            ts.append(float(tok))
        except ValueError:
            pass
    if len(ts) < 2:
        return None
    ts.sort()   # decode order != presentation order when there are B-frames
    return max(b - a for a, b in zip(ts, ts[1:]))


def _clean(text):
    # YouTube rejects < and > in titles and descriptions; one bad title would fail
    # every run at the same VOD and starve the queue behind it.
    return text.replace("<", "\u2039").replace(">", "\u203a")


def upload(yt, vod, path, part=None, parts=None):
    label = f" (Part {part}/{parts})" if part and parts and parts > 1 else ""
    body = {
        "snippet": {
            "title": _clean(f"[{vod['created_at'][:10]}] {vod['title']}")[:100 - len(label)] + label,
            "description": _clean(
                f"Twitch VOD archive.\n\n"
                f"Streamed: {vod['created_at']}\n"
                f"Duration: {vod['duration']}\n"
                f"Original: {vod['url']}\n"
                f"Twitch id: {vod['id']}\n"
                + (f"Part {part} of {parts} (too long for one file on the archive runner)\n" if label else "")
            )[:5000],
            # 20 = Gaming. Avoids YouTube guessing.
            "categoryId": "20",
        },
        "status": {"privacyStatus": "private", "selfDeclaredMadeForKids": False},
    }
    media = MediaFileUpload(path, chunksize=8 * 1024 * 1024, resumable=True)
    req = yt.videos().insert(part="snippet,status", body=body, media_body=media)

    response, tries = None, 0
    while response is None:
        try:
            _, response = req.next_chunk()
            tries = 0   # the budget is per run of CONSECUTIVE failures, not per file: a 22 GB
                        # upload is ~2,750 chunks and six unrelated blips must not kill it
        except HttpError as exc:
            text = str(exc).lower()
            if any(k in text for k in ("quotaexceeded", "uploadlimitexceeded", "dailylimitexceeded")):
                raise QuotaStop(str(exc)[:200]) from exc
            status = getattr(getattr(exc, "resp", None), "status", None)
            if status in (400, 401, 403, 404):
                raise   # not transient; retrying only wastes time
            tries += 1
            if tries > 5:
                raise
            log(f"  chunk failed ({exc}), retry {tries}/5")
            time.sleep(2 ** tries)
        except Exception as exc:  # noqa: BLE001 - resumable uploads fail transiently
            tries += 1
            if tries > 5:
                raise
            log(f"  chunk failed ({exc}), retry {tries}/5")
            time.sleep(2 ** tries)
    return response["id"]


def notify(vod, video_id, size, part=None, parts=None):
    if not (WORKER and WORKER_TOKEN):
        return
    label = f" (Part {part}/{parts})" if part and parts and parts > 1 else ""
    try:
        requests.post(f"{WORKER}/vod", timeout=20,
            headers={"Authorization": f"Bearer {WORKER_TOKEN}"},
            json={
                "who": WHO,
                "title": vod["title"] + label,
                "game": vod.get("game_name") or "",
                "duration": parse_duration(vod["duration"]),
                "bytes": size,
                "streamed_at": int(datetime.fromisoformat(
                    vod["created_at"].replace("Z", "+00:00")).timestamp()),
                "url": f"https://youtu.be/{video_id}",
            })
    except Exception as exc:  # noqa: BLE001 - a failed card must not fail the archive
        log(f"  card post failed (upload was fine): {exc}")


def entries_for(done, twitch_id):
    return [d for d in done if isinstance(d, dict) and d.get("twitch_id") == twitch_id]


def completed_ids(done):
    """A VOD is done when every one of its parts is recorded. Entries with no
    "parts" field (every entry written before slicing existed) count as whole."""
    ids, partial = set(), {}
    for d in done:
        if not isinstance(d, dict):
            ids.add(d)
            continue
        n = d.get("parts") or 1
        if n <= 1:
            ids.add(d["twitch_id"])
        else:
            partial.setdefault(d["twitch_id"], {"n": n, "have": set()})["have"].add(d.get("part"))
    for tid, p in partial.items():
        if len(p["have"]) >= p["n"]:
            ids.add(tid)
    return ids


def main():
    done = load_manifest()
    done_ids = completed_ids(done)

    vods = twitch_vods(twitch_token())
    cutoff = datetime.now(timezone.utc) - timedelta(minutes=MIN_AGE_MINUTES)

    pending = []
    for v in vods:
        if v["id"] in done_ids:
            continue
        created = datetime.fromisoformat(v["created_at"].replace("Z", "+00:00"))
        if created > cutoff:
            log(f"skip {v['id']}: too fresh, Twitch may still be writing it")
            continue
        # created_at is when the stream STARTED. A VOD that is still growing (or ended a
        # few minutes ago) would be archived as if complete and the rest never captured.
        if created + timedelta(seconds=parse_duration(v["duration"])) > cutoff:
            log(f"skip {v['id']}: stream still live or only just ended")
            continue
        if v.get("status") == "recording" or v.get("thumbnail_url", "").find("404_processing") != -1:
            log(f"skip {v['id']}: still recording")
            continue
        pending.append(v)

    pending.sort(key=lambda v: v["created_at"])  # oldest first: they expire first
    log(f"{len(vods)} VODs on Twitch, {len(done_ids)} already archived, {len(pending)} to do")

    if not pending:
        log("nothing to archive")
        return

    yt = youtube()
    playlist_id = get_or_create_playlist(yt)
    used = 0
    uploaded_units = 0   # parts (or whole VODs) uploaded this run
    out_of_time = False
    stop_all = False
    failures = []

    # Never trust the workspace. A previous run that died mid-download leaves
    # tens of GB of debris; on a fresh runner this is a no-op.
    log(f"free disk at start: {free_bytes() / 1e9:.1f} GB (wiped {wipe_temp()} leftover files)")

    for v in pending:
        if time.time() > DEADLINE:
            out_of_time = True   # a run that simply ran out of time is normal, not a failure
        if out_of_time or stop_all:
            log("stopping: approaching job time limit or YouTube's daily limit, rest go next run")
            break
        if used > MAX_BYTES_PER_RUN:
            log("stopping: byte backstop for this run used, rest go next run")
            break

        dur = parse_duration(v["duration"])
        log(f"\n=== {v['id']}  {v['created_at'][:10]}  {v['duration']}  {v['title'][:60]}")
        try:
            wipe_temp()
            rate = probe_rate(v)
            have = entries_for(done, v["id"])
            resumed = have and (have[0].get("parts") or 1) > 1
            if resumed:
                # Resume with the ORIGINAL plan. Re-planning from today's free
                # space could cut the slices somewhere else and mismatch the
                # parts already uploaded.
                n, chunk = have[0]["parts"], have[0]["chunk_s"]
                plan = [(i * chunk, min(dur, (i + 1) * chunk)) for i in range(n) if i * chunk < dur]
                have_parts = {e.get("part") for e in have}
            else:
                try:
                    plan = plan_slices(dur, rate, free_bytes())
                except RuntimeError as exc:
                    log(f"  skipping this VOD for now: {exc}")
                    continue
                if plan and not shutil.which("ffmpeg"):
                    # Slicing is done by ffmpeg. Say so plainly and cheaply, rather
                    # than fail every slice. The workflow installs it; if this ever
                    # prints, that step broke.
                    log("  needs time slices but ffmpeg is not installed; skipping this VOD for now")
                    continue
                have_parts = set()
            chunk_s = (plan[0][1] - plan[0][0]) if plan else None
            parts = plan or [(None, None)]
            multi = len(parts) > 1
            log(f"  size ~{dur * rate / 1e9:.1f} GB at {rate / 1e6:.2f} MB/s; "
                + (f"{len(parts)} slice(s) of ~{chunk_s / 3600:.1f}h" if plan else "downloading whole"))

            for idx, (a, b) in enumerate(parts, 1):
                if multi and idx in have_parts:
                    continue
                expected = (b - a) if a is not None else dur
                need = expected * rate
                if time.time() > DEADLINE or would_overrun(need):
                    out_of_time = True
                    log("  not enough time left in this run for the next piece; it goes next run")
                    break
                wipe_temp()
                if a is not None and need * SLICE_FACTOR > free_bytes() - DISK_SAFETY:
                    log(f"  slice {idx}/{len(parts)} no longer fits ({free_bytes() / 1e9:.1f} GB free); next run")
                    break

                path = os.path.join(HERE, f"_tmp_{v['id']}.mp4")
                if multi:
                    log(f"  -- part {idx}/{len(parts)}  {a / 3600:.2f}h -> {b / 3600:.2f}h")
                ok = False
                for attempt in (1, 2):
                    got = download(v, path, a, b, expect_bytes=need)
                    if not got:
                        break
                    if a is not None:
                        expected = got   # cut on segment boundaries: a few seconds over b - a
                    if not looks_complete(path, expected, min_bytes=int(need * 0.5)):
                        break
                    ok = True
                    if a is None:
                        break   # native downloads retry fragments and fail LOUDLY on their own
                    gap = biggest_gap(path)
                    if gap is None or gap <= 1.0:
                        break
                    log(f"  HOLE: {gap:.1f}s of footage missing inside this slice "
                        f"(a segment was lost in transit)")
                    if attempt == 1:
                        log("  downloading the slice once more")
                        wipe_temp()
                        ok = False
                        continue
                    log("  still holed after a retry: uploading anyway. A copy missing a few "
                        "seconds is better than losing the stream when Twitch deletes it")
                if not ok:
                    break
                size = os.path.getsize(path)
                log(f"  downloaded {size / 1e9:.1f} GB, uploading")
                vid = upload(yt, v, path, idx if multi else None, len(parts) if multi else None)
                log(f"  uploaded as {vid} (private)")

                if add_to_playlist(yt, playlist_id, vid):
                    log(f"  added to '{PLAYLIST_TITLE}'")

                entry = {"twitch_id": v["id"], "youtube_id": vid,
                         "title": v["title"], "archived": datetime.now(timezone.utc).isoformat()}
                if multi:
                    entry.update({"part": idx, "parts": len(parts), "chunk_s": chunk_s})
                done.append(entry)
                save_manifest(done)
                checkpoint_manifest()
                notify(v, vid, size, idx if multi else None, len(parts) if multi else None)
                used += size
                uploaded_units += 1
                wipe_temp()
        except QuotaStop as exc:
            log(f"  YouTube says stop for today: {exc}. Resuming at the next scheduled run.")
            stop_all = True
        except Exception as exc:  # noqa: BLE001 - one bad VOD must not abandon the queue behind it
            failures.append(v["id"])
            log(f"  FAILED {v['id']}: {type(exc).__name__}: {str(exc)[:300]}")
        finally:
            wipe_temp()

    # Tell the workflow whether to run itself again. Continuing only when
    # progress was actually made means a persistent failure stops the loop
    # instead of re-triggering forever.
    completed = completed_ids(done)
    remaining = sum(1 for v in pending if v["id"] not in completed)
    log(f"\nuploaded {uploaded_units} file(s) this run, {remaining} VOD(s) still outstanding")

    step_out = os.environ.get("GITHUB_OUTPUT")
    if step_out:
        with open(step_out, "a", encoding="utf-8") as fh:
            fh.write(f"archived={uploaded_units}\n")
            fh.write(f"remaining={remaining}\n")
            fh.write(f"continue={'yes' if remaining > 0 and uploaded_units > 0 and not stop_all else 'no'}\n")

    log("done")

    # Exit non-zero when work is outstanding and NOTHING moved, or anything failed, so
    # GitHub marks the run failed and emails. The two-week outage was silent because
    # every run exited 0 while archiving nothing.
    if failures or (remaining > 0 and uploaded_units == 0 and not out_of_time):
        log(f"ERROR: {len(failures)} VOD(s) failed, {remaining} outstanding, {uploaded_units} uploaded. "
            f"Failing this run on purpose so it is not silent.")
        sys.exit(1)


if __name__ == "__main__":
    main()
