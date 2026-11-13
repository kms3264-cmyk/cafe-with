/* QR 코드 생성기 (바이트 모드, 오류정정 M, 버전 1~10). 외부 라이브러리 없이 동작합니다. */
(function () {
  var EXP = new Uint8Array(512), LOG = new Uint8Array(256), v = 1, i;
  for (i = 0; i < 255; i++) { EXP[i] = v; LOG[v] = i; v <<= 1; if (v & 256) v ^= 0x11d; }
  for (i = 255; i < 512; i++) EXP[i] = EXP[i - 255];
  function mul(a, b) { return a && b ? EXP[LOG[a] + LOG[b]] : 0; }

  // [블록당 오류정정 수, 그룹1 블록 수, 그룹1 데이터 수, 그룹2 블록 수, 그룹2 데이터 수]
  var BLOCKS = [null,
    [10, 1, 16, 0, 0], [16, 1, 28, 0, 0], [26, 1, 44, 0, 0], [18, 2, 32, 0, 0], [24, 2, 43, 0, 0],
    [16, 4, 27, 0, 0], [18, 4, 31, 0, 0], [22, 2, 38, 2, 39], [22, 3, 36, 2, 37], [26, 4, 43, 1, 44]];
  var ALIGN = [null, [], [6, 18], [6, 22], [6, 26], [6, 30], [6, 34], [6, 22, 38], [6, 24, 42], [6, 26, 46], [6, 28, 50]];

  function rsGenerator(deg) {
    var g = [1];
    for (var n = 0; n < deg; n++) {
      var next = new Array(g.length + 1).fill(0);
      for (var j = 0; j < g.length; j++) { next[j] ^= g[j]; next[j + 1] ^= mul(g[j], EXP[n]); }
      g = next;
    }
    return g;
  }
  function rsRemainder(data, deg) {
    var g = rsGenerator(deg), r = new Array(deg).fill(0);
    data.forEach(function (b) {
      var f = b ^ r.shift();
      r.push(0);
      for (var j = 0; j < deg; j++) r[j] ^= mul(g[j + 1], f);
    });
    return r;
  }

  function codewords(bytes, ver) {
    var b = BLOCKS[ver], capacity = b[1] * b[2] + b[3] * b[4];
    var bits = [];
    function put(val, len) { for (var k = len - 1; k >= 0; k--) bits.push((val >>> k) & 1); }
    put(4, 4); put(bytes.length, ver < 10 ? 8 : 16);
    bytes.forEach(function (x) { put(x, 8); });
    put(0, Math.min(4, capacity * 8 - bits.length));
    while (bits.length % 8) bits.push(0);
    var data = [];
    for (var p = 0; p < bits.length; p += 8) {
      var byte = 0;
      for (var q = 0; q < 8; q++) byte = (byte << 1) | bits[p + q];
      data.push(byte);
    }
    for (var pad = 0xEC; data.length < capacity; pad ^= 0xEC ^ 0x11) data.push(pad);

    var blocks = [], eccs = [], pos = 0;
    for (var n = 0; n < b[1] + b[3]; n++) {
      var len = n < b[1] ? b[2] : b[4], blk = data.slice(pos, pos + len);
      pos += len; blocks.push(blk); eccs.push(rsRemainder(blk, b[0]));
    }
    var out = [], longest = Math.max(b[2], b[4]);
    for (var c = 0; c < longest; c++) blocks.forEach(function (x) { if (c < x.length) out.push(x[c]); });
    for (var e = 0; e < b[0]; e++) eccs.forEach(function (x) { out.push(x[e]); });
    return out;
  }

  function maskBit(m, x, y) {
    switch (m) {
      case 0: return (x + y) % 2 === 0;
      case 1: return y % 2 === 0;
      case 2: return x % 3 === 0;
      case 3: return (x + y) % 3 === 0;
      case 4: return (Math.floor(x / 3) + Math.floor(y / 2)) % 2 === 0;
      case 5: return x * y % 2 + x * y % 3 === 0;
      case 6: return (x * y % 2 + x * y % 3) % 2 === 0;
      default: return ((x + y) % 2 + x * y % 3) % 2 === 0;
    }
  }

  function build(ver, words, mask) {
    var size = ver * 4 + 17, mod = [], fn = [], y, x;
    for (y = 0; y < size; y++) { mod.push(new Array(size).fill(false)); fn.push(new Array(size).fill(false)); }
    function set(cx, cy, on) { mod[cy][cx] = on; fn[cy][cx] = true; }

    for (i = 0; i < size; i++) { set(6, i, i % 2 === 0); set(i, 6, i % 2 === 0); }
    [[3, 3], [size - 4, 3], [3, size - 4]].forEach(function (c) {
      for (var dy = -4; dy <= 4; dy++) for (var dx = -4; dx <= 4; dx++) {
        var px = c[0] + dx, py = c[1] + dy, d = Math.max(Math.abs(dx), Math.abs(dy));
        if (px >= 0 && px < size && py >= 0 && py < size) set(px, py, d !== 2 && d !== 4);
      }
    });
    var al = ALIGN[ver];
    al.forEach(function (ay, a) {
      al.forEach(function (ax, b) {
        var corner = (a === 0 && b === 0) || (a === 0 && b === al.length - 1) || (a === al.length - 1 && b === 0);
        if (corner) return;
        for (var dy = -2; dy <= 2; dy++) for (var dx = -2; dx <= 2; dx++)
          set(ax + dx, ay + dy, Math.max(Math.abs(dx), Math.abs(dy)) !== 1);
      });
    });

    // 형식 정보 (오류정정 M = 00)
    var fd = mask, rem = fd;
    for (i = 0; i < 10; i++) rem = (rem << 1) ^ ((rem >>> 9) * 0x537);
    var fbits = ((fd << 10) | rem) ^ 0x5412;
    function fb(n) { return ((fbits >>> n) & 1) !== 0; }
    for (i = 0; i <= 5; i++) set(8, i, fb(i));
    set(8, 7, fb(6)); set(8, 8, fb(7)); set(7, 8, fb(8));
    for (i = 9; i < 15; i++) set(14 - i, 8, fb(i));
    for (i = 0; i < 8; i++) set(size - 1 - i, 8, fb(i));
    for (i = 8; i < 15; i++) set(8, size - 15 + i, fb(i));
    set(8, size - 8, true);

    if (ver >= 7) {
      var vr = ver;
      for (i = 0; i < 12; i++) vr = (vr << 1) ^ ((vr >>> 11) * 0x1F25);
      var vbits = (ver << 12) | vr;
      for (i = 0; i < 18; i++) {
        var on = ((vbits >>> i) & 1) !== 0, a2 = size - 11 + i % 3, b2 = Math.floor(i / 3);
        set(a2, b2, on); set(b2, a2, on);
      }
    }

    var idx = 0;
    for (var right = size - 1; right >= 1; right -= 2) {
      if (right === 6) right = 5;
      for (var vert = 0; vert < size; vert++) for (var j = 0; j < 2; j++) {
        x = right - j;
        y = ((right + 1) & 2) === 0 ? size - 1 - vert : vert;
        if (fn[y][x]) continue;
        var bit = idx < words.length * 8 && ((words[idx >>> 3] >>> (7 - (idx & 7))) & 1) !== 0;
        idx++;
        mod[y][x] = bit !== maskBit(mask, x, y);
      }
    }
    return mod;
  }

  function penalty(m) {
    var size = m.length, score = 0, dark = 0, x, y;
    for (y = 0; y < size; y++) {
      var runR = 1, runC = 1;
      for (x = 0; x < size; x++) {
        if (m[y][x]) dark++;
        if (x > 0) {
          if (m[y][x] === m[y][x - 1]) { runR++; if (runR === 5) score += 3; else if (runR > 5) score++; } else runR = 1;
          if (m[x][y] === m[x - 1][y]) { runC++; if (runC === 5) score += 3; else if (runC > 5) score++; } else runC = 1;
        }
        if (x > 0 && y > 0 && m[y][x] === m[y][x - 1] && m[y][x] === m[y - 1][x] && m[y][x] === m[y - 1][x - 1]) score += 3;
      }
    }
    return score + Math.floor(Math.abs(dark * 100 / (size * size) - 50) / 5) * 10;
  }

  function encode(text) {
    var bytes = Array.from(new TextEncoder().encode(text)), ver = 1;
    function fits(n) {
      var b = BLOCKS[n];
      return 4 + (n < 10 ? 8 : 16) + bytes.length * 8 <= (b[1] * b[2] + b[3] * b[4]) * 8;
    }
    while (ver <= 10 && !fits(ver)) ver++;
    if (ver > 10) throw new Error("주소가 너무 길어서 QR을 만들 수 없습니다.");
    var words = codewords(bytes, ver), best = null, bestScore = Infinity;
    for (var mask = 0; mask < 8; mask++) {
      var m = build(ver, words, mask), s = penalty(m);
      if (s < bestScore) { best = m; bestScore = s; }
    }
    return best;
  }

  function svg(text, label) {
    var m = encode(text), size = m.length, q = 4, d = "";
    for (var y = 0; y < size; y++) for (var x = 0; x < size; x++)
      if (m[y][x]) d += "M" + (x + q) + " " + (y + q) + "h1v1h-1z";
    var n = size + q * 2;
    return '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ' + n + " " + n + '" role="img" aria-label="' +
      (label || "QR 코드") + '" shape-rendering="crispEdges"><rect width="' + n + '" height="' + n +
      '" fill="#fff"/><path d="' + d + '" fill="#000"/></svg>';
  }

  window.QR = { encode: encode, svg: svg };
})();
