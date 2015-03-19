#!/usr/bin/python3
# -*- coding: utf-8 -*-

import re, os, sys, urllib.parse, hashlib, http.client, base64, datetime, functools, time, random, subprocess
_SVGNS     = 'xmlns="http://www.w3.org/2000/svg"'

##### ENCODING #####
PAD = lambda s:(len(s)%2)*'0'+s[2:]

def i2b(x, n=1):
    "int to bytes with n padding"
    z = bytes.fromhex(PAD(hex(x)))
    return ((n-len(z))%n)*bytes.fromhex('00') + z

def b2i(x):
    "bytes to int"
    return int.from_bytes(x, 'big')

def s2b(x, n=1):
    "signed int to bytes with n padding"
    z = bytes.fromhex(PAD(hex(x + (1<<(8*n-1)))))
    return ((n-len(z))%n)*bytes.fromhex('00') + z

def b2s(x, n=1):
    "signed bytes to int"
    return int.from_bytes(x, 'big') - (1<<(8*n-1)) 

def itob64(n):
    "transform int to base64"
    return re.sub(b'=*$', b'', base64.urlsafe_b64encode(bytes.fromhex(PAD(hex(n)))))

def b64toi(c):
    "transform base64 to int"
    if c == '': return 0
    return int.from_bytes(base64.urlsafe_b64decode(c + b'='*((4-(len(c)%4))%4)), 'big')

def btob64(c):
    "bytes to base64"
    return base64.urlsafe_b64encode(c).decode('ascii').strip('=')

def b64tob(c):
    "base64 to bytes"
    return base64.urlsafe_b64decode(c + b'='*((4-(len(c)%4))%4))

##### QRCODE #####

ERR_COR_L, ERR_COR_M, ERR_COR_Q, ERR_COR_H = 1, 0, 3, 2
MODE_NUMBER, MODE_ALPHA_NUM, MODE_8BIT_BYTE, MODE_KANJI = 1, 2, 4, 8
MODE_SIZE_SMALL  = { MODE_NUMBER: 10, MODE_ALPHA_NUM: 9,  MODE_8BIT_BYTE: 8,  MODE_KANJI: 8,}
MODE_SIZE_MEDIUM = { MODE_NUMBER: 12, MODE_ALPHA_NUM: 11, MODE_8BIT_BYTE: 16, MODE_KANJI: 10,}
MODE_SIZE_LARGE  = { MODE_NUMBER: 14, MODE_ALPHA_NUM: 13, MODE_8BIT_BYTE: 16, MODE_KANJI: 12,}
ALPHA_NUM = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%*+-./:'
TEXP = list(range(256))
TLOG = list(range(256))
for i in range(8): TEXP[i] = 1 << i
for i in range(8, 256): TEXP[i] = (TEXP[i - 4] ^ TEXP[i - 5] ^ TEXP[i - 6] ^ TEXP[i - 8])
for i in range(255): TLOG[TEXP[i]] = i
NUMBER_LENGTH = {3: 10, 2: 7, 1: 4}
RS_BLOCK_OFFSET = { ERR_COR_L: 0, ERR_COR_M: 1, ERR_COR_Q: 2, ERR_COR_H: 3 }
RS_BLOCK_TABLE = [ # L M Q H
    [1, 26, 19], [1, 26, 16], [1, 26, 13], [1, 26, 9],
    [1, 44, 34], [1, 44, 28], [1, 44, 22], [1, 44, 16],
    [1, 70, 55], [1, 70, 44], [2, 35, 17], [2, 35, 13],
    [1, 100, 80],[2, 50, 32], [2, 50, 24], [4, 25, 9],
    [1, 134, 108], [2, 67, 43], [2, 33, 15, 2, 34, 16], [2, 33, 11, 2, 34, 12], 
    [2, 86, 68], [4, 43, 27], [4, 43, 19], [4, 43, 15], 
    [2, 98, 78], [4, 49, 31], [2, 32, 14, 4, 33, 15], [4, 39, 13, 1, 40, 14], 
    [2, 121, 97], [2, 60, 38, 2, 61, 39], [4, 40, 18, 2, 41, 19], [4, 40, 14, 2, 41, 15], 
    [2, 146, 116], [3, 58, 36, 2, 59, 37], [4, 36, 16, 4, 37, 17], [4, 36, 12, 4, 37, 13], 
    [2, 86, 68, 2, 87, 69], [4, 69, 43, 1, 70, 44], [6, 43, 19, 2, 44, 20], [6, 43, 15, 2, 44, 16], 
    [4, 101, 81], [1, 80, 50, 4, 81, 51], [4, 50, 22, 4, 51, 23], [3, 36, 12, 8, 37, 13], 
    [2, 116, 92, 2, 117, 93], [6, 58, 36, 2, 59, 37], [4, 46, 20, 6, 47, 21], [7, 42, 14, 4, 43, 15], 
    [4, 133, 107], [8, 59, 37, 1, 60, 38], [8, 44, 20, 4, 45, 21], [12, 33, 11, 4, 34, 12], 
    [3, 145, 115, 1, 146, 116], [4, 64, 40, 5, 65, 41], [11, 36, 16, 5, 37, 17], [11, 36, 12, 5, 37, 13], 
    [5, 109, 87, 1, 110, 88], [5, 65, 41, 5, 66, 42], [5, 54, 24, 7, 55, 25], [11, 36, 12], 
    [5, 122, 98, 1, 123, 99], [7, 73, 45, 3, 74, 46], [15, 43, 19, 2, 44, 20], [3, 45, 15, 13, 46, 16], 
    [1, 135, 107, 5, 136, 108], [10, 74, 46, 1, 75, 47], [1, 50, 22, 15, 51, 23], [2, 42, 14, 17, 43, 15], 
    [5, 150, 120, 1, 151, 121], [9, 69, 43, 4, 70, 44], [17, 50, 22, 1, 51, 23], [2, 42, 14, 19, 43, 15], 
    [3, 141, 113, 4, 142, 114], [3, 70, 44, 11, 71, 45], [17, 47, 21, 4, 48, 22], [9, 39, 13, 16, 40, 14], 
    [3, 135, 107, 5, 136, 108], [3, 67, 41, 13, 68, 42], [15, 54, 24, 5, 55, 25], [15, 43, 15, 10, 44, 16], 
    [4, 144, 116, 4, 145, 117], [17, 68, 42], [17, 50, 22, 6, 51, 23], [19, 46, 16, 6, 47, 17], 
    [2, 139, 111, 7, 140, 112], [17, 74, 46], [7, 54, 24, 16, 55, 25], [34, 37, 13], 
    [4, 151, 121, 5, 152, 122], [4, 75, 47, 14, 76, 48], [11, 54, 24, 14, 55, 25], [16, 45, 15, 14, 46, 16], 
    [6, 147, 117, 4, 148, 118], [6, 73, 45, 14, 74, 46], [11, 54, 24, 16, 55, 25], [30, 46, 16, 2, 47, 17], 
    [8, 132, 106, 4, 133, 107], [8, 75, 47, 13, 76, 48], [7, 54, 24, 22, 55, 25], [22, 45, 15, 13, 46, 16], 
    [10, 142, 114, 2, 143, 115], [19, 74, 46, 4, 75, 47], [28, 50, 22, 6, 51, 23], [33, 46, 16, 4, 47, 17], 
    [8, 152, 122, 4, 153, 123], [22, 73, 45, 3, 74, 46], [8, 53, 23, 26, 54, 24], [12, 45, 15, 28, 46, 16], 
    [3, 147, 117, 10, 148, 118], [3, 73, 45, 23, 74, 46], [4, 54, 24, 31, 55, 25], [11, 45, 15, 31, 46, 16], 
    [7, 146, 116, 7, 147, 117], [21, 73, 45, 7, 74, 46], [1, 53, 23, 37, 54, 24], [19, 45, 15, 26, 46, 16], 
    [5, 145, 115, 10, 146, 116], [19, 75, 47, 10, 76, 48], [15, 54, 24, 25, 55, 25], [23, 45, 15, 25, 46, 16], 
    [13, 145, 115, 3, 146, 116], [2, 74, 46, 29, 75, 47], [42, 54, 24, 1, 55, 25], [23, 45, 15, 28, 46, 16], 
    [17, 145, 115], [10, 74, 46, 23, 75, 47], [10, 54, 24, 35, 55, 25], [19, 45, 15, 35, 46, 16], 
    [17, 145, 115, 1, 146, 116], [14, 74, 46, 21, 75, 47], [29, 54, 24, 19, 55, 25], [11, 45, 15, 46, 46, 16], 
    [13, 145, 115, 6, 146, 116], [14, 74, 46, 23, 75, 47], [44, 54, 24, 7, 55, 25], [59, 46, 16, 1, 47, 17], 
    [12, 151, 121, 7, 152, 122], [12, 75, 47, 26, 76, 48], [39, 54, 24, 14, 55, 25], [22, 45, 15, 41, 46, 16], 
    [6, 151, 121, 14, 152, 122], [6, 75, 47, 34, 76, 48], [46, 54, 24, 10, 55, 25], [2, 45, 15, 64, 46, 16],
    [17, 152, 122, 4, 153, 123], [29, 74, 46, 14, 75, 47], [49, 54, 24, 10, 55, 25], [24, 45, 15, 46, 46, 16],
    [4, 152, 122, 18, 153, 123], [13, 74, 46, 32, 75, 47], [48, 54, 24, 14, 55, 25], [42, 45, 15, 32, 46, 16],
    [20, 147, 117, 4, 148, 118], [40, 75, 47, 7, 76, 48], [43, 54, 24, 22, 55, 25], [10, 45, 15, 67, 46, 16],
    [19, 148, 118, 6, 149, 119], [18, 75, 47, 31, 76, 48], [34, 54, 24, 34, 55, 25], [20, 45, 15, 61, 46, 16]
]
PATTERN_POSITION_TABLE = [
    [], [6, 18], [6, 22], [6, 26], [6, 30], [6, 34],
    [6, 22, 38], [6, 24, 42], [6, 26, 46], [6, 28, 50], [6, 30, 54], [6, 32, 58], [6, 34, 62],
    [6, 26, 46, 66], [6, 26, 48, 70], [6, 26, 50, 74], [6, 30, 54, 78], [6, 30, 56, 82], [6, 30, 58, 86], [6, 34, 62, 90],
    [6, 28, 50, 72, 94], [6, 26, 50, 74, 98], [6, 30, 54, 78, 102], [6, 28, 54, 80, 106], [6, 32, 58, 84, 110], [6, 30, 58, 86, 114], [6, 34, 62, 90, 118],
    [6, 26, 50, 74, 98, 122], [6, 30, 54, 78, 102, 126], [6, 26, 52, 78, 104, 130], [6, 30, 56, 82, 108, 134],
    [6, 34, 60, 86, 112, 138], [6, 30, 58, 86, 114, 142], [6, 34, 62, 90, 118, 146],
    [6, 30, 54, 78, 102, 126, 150], [6, 24, 50, 76, 102, 128, 154], [6, 28, 54, 80, 106, 132, 158], [6, 32, 58, 84, 110, 136, 162],
    [6, 26, 54, 82, 110, 138, 166], [6, 30, 58, 86, 114, 142, 170]
]
G15 = ((1 << 10) | (1 << 8) | (1 << 5) | (1 << 4) | (1 << 2) | (1 << 1) | (1 << 0))
G18 = ((1 << 12) | (1 << 11) | (1 << 10) | (1 << 9) | (1 << 8) | (1 << 5) | (1 << 2) | (1 << 0))
G15_MASK = (1 << 14) | (1 << 12) | (1 << 10) | (1 << 4) | (1 << 1)

def BCH_type_info(data):
    d = data << 10
    while BCH_digit(d) - BCH_digit(G15) >= 0: d ^= (G15 << (BCH_digit(d) - BCH_digit(G15)))
    return ((data << 10) | d) ^ G15_MASK

def BCH_type_number(data):
    d = data << 12
    while BCH_digit(d) - BCH_digit(G18) >= 0: d ^= (G18 << (BCH_digit(d) - BCH_digit(G18)))
    return (data << 12) | d

def BCH_digit(data):
    digit = 0
    while data != 0:
        digit += 1
        data >>= 1
    return digit

def pattern_position(version):
    return PATTERN_POSITION_TABLE[version - 1]

def mask_func(pattern):
    if pattern == 0: return lambda i, j: (i + j) % 2 == 0 
    if pattern == 1: return lambda i, j: i % 2 == 0 
    if pattern == 2: return lambda i, j: j % 3 == 0
    if pattern == 3: return lambda i, j: (i + j) % 3 == 0
    if pattern == 4: return lambda i, j: (int(i / 2) + int(j / 3)) % 2 == 0
    if pattern == 5: return lambda i, j: (i * j) % 2 + (i * j) % 3 == 0
    if pattern == 6: return lambda i, j: ((i * j) % 2 + (i * j) % 3) % 2 == 0
    if pattern == 7: return lambda i, j: ((i * j) % 3 + (i + j) % 2) % 2 == 0

def length_in_bits(mode, version):
    if version < 10: mode_size = MODE_SIZE_SMALL
    elif version < 27: mode_size = MODE_SIZE_MEDIUM
    else: mode_size = MODE_SIZE_LARGE
    return mode_size[mode]

def lost_point1(modules):
    modules_count, lost_point, darkCount = len(modules), 0, 0
    for row in range(modules_count):
        for col in range(modules_count):
            sameCount, dark = 0, modules[row][col]
            for r in range(-1, 2):
                if row + r < 0 or modules_count <= row + r: continue
                for c in range(-1, 2):
                    if col + c < 0 or modules_count <= col + c: continue
                    if r == 0 and c == 0: continue
                    if dark == modules[row + r][col + c]: sameCount += 1
            if sameCount > 5: lost_point += (3 + sameCount - 5)
    for row in range(modules_count - 1):
        for col in range(modules_count - 1):
            count = 0
            if modules[row][col]: count += 1
            if modules[row + 1][col]: count += 1
            if modules[row][col + 1]: count += 1
            if modules[row + 1][col + 1]: count += 1
            if count == 0 or count == 4: lost_point += 3
    for row in range(modules_count):
        for col in range(modules_count - 6):
            if (modules[row][col]
                    and not modules[row][col + 1]
                    and modules[row][col + 2]
                    and modules[row][col + 3]
                    and modules[row][col + 4]
                    and not modules[row][col + 5]
                    and modules[row][col + 6]):
                lost_point += 40
    for col in range(modules_count):
        for row in range(modules_count - 6):
            if (modules[row][col]
                    and not modules[row + 1][col]
                    and modules[row + 2][col]
                    and modules[row + 3][col]
                    and modules[row + 4][col]
                    and not modules[row + 5][col]
                    and modules[row + 6][col]):
                lost_point += 40
    for col in range(modules_count):
        for row in range(modules_count):
            if modules[row][col]: darkCount += 1
    return lost_point + abs(100 * darkCount / modules_count / modules_count - 50) * 2

class QRData:
    def __init__(self, data, mode=None):
        if data.isdigit(): auto_mode = MODE_NUMBER
        elif re.match('^[%s]*$' % re.escape(ALPHA_NUM), data): auto_mode = MODE_ALPHA_NUM
        else: auto_mode = MODE_8BIT_BYTE
        self.mode, self.data = auto_mode if mode is None else mode, data
    def __len__(self):
        return len(self.data)
    def write(self, buffer):
        if self.mode == MODE_NUMBER:
            for i in range(0, len(self.data), 3):
                chars = self.data[i:i + 3]
                bit_length = NUMBER_LENGTH[len(chars)]
                buffer.put(int(chars), bit_length)
        elif self.mode == MODE_ALPHA_NUM:
            for i in range(0, len(self.data), 2):
                chars = self.data[i:i + 2]
                if len(chars) > 1: buffer.put(ALPHA_NUM.find(chars[0]) * 45 + ALPHA_NUM.find(chars[1]), 11)
                else: buffer.put(ALPHA_NUM.find(chars), 6)
        else:
            for c in self.data:
                buffer.put(ord(c), 8)

class BitBuffer:
    def __init__(self): self.buffer, self.length = [], 0
    def get(self, index): return ((self.buffer[int(index/8)] >> (7 - index % 8)) & 1) == 1
    def put(self, num, length): 
        for i in range(length): self.put_bit(((num >> (length - i - 1)) & 1) == 1)
    def __len__(self): return self.length
    def put_bit(self, bit):
        buf_index = self.length // 8
        if len(self.buffer) <= buf_index: self.buffer.append(0)
        if bit: self.buffer[buf_index] |= (0x80 >> (self.length % 8))
        self.length += 1

def create_bytes(buffer, rs_b):
    offset, maxDcCount, maxEcCount, totalCodeCount, dcdata, ecdata = 0, 0, 0, 0, [0] * len(rs_b), [0] * len(rs_b)
    for r in range(len(rs_b)):
        dcCount = rs_b[r].data_count
        ecCount = rs_b[r].total_count - dcCount
        maxDcCount, maxEcCount, dcdata[r] = max(maxDcCount, dcCount), max(maxEcCount, ecCount), [0] * dcCount
        for i in range(len(dcdata[r])): dcdata[r][i] = 0xff & buffer.buffer[i + offset]
        offset += dcCount
        rsPoly = Poly([1], 0) 
        for i in range(ecCount): rsPoly = rsPoly * Poly([1, TEXP[i]], 0)
        modPoly = Poly(dcdata[r], len(rsPoly) - 1) % rsPoly
        ecdata[r] = [0] * (len(rsPoly) - 1)
        for i in range(len(ecdata[r])):
            modIndex = i + len(modPoly) - len(ecdata[r])
            ecdata[r][i] = modPoly[modIndex] if (modIndex >= 0) else 0
    for b in rs_b: totalCodeCount += b.total_count
    data, index = [None] * totalCodeCount, 0
    for i in range(maxDcCount):
        for r in range(len(rs_b)):
            if i < len(dcdata[r]):
                data[index] = dcdata[r][i]
                index += 1
    for i in range(maxEcCount):
        for r in range(len(rs_b)):
            if i < len(ecdata[r]):
                data[index] = ecdata[r][i]
                index += 1
    return data

class DataOverflowError(Exception):
    pass

def create_data(version, error_correction, data_list):
    rs_b, buffer, total_data_count, PAD0, PAD1 = rs_blocks(version, error_correction), BitBuffer(), 0, 0xEC, 0x11
    for data in data_list:
        buffer.put(data.mode, 4)
        buffer.put(len(data), length_in_bits(data.mode, version))
        data.write(buffer)
    for block in rs_b: total_data_count += block.data_count
    if len(buffer) > total_data_count * 8: raise DataOverflowError()
    if len(buffer) + 4 <= total_data_count * 8: buffer.put(0, 4)
    while len(buffer) % 8: buffer.put_bit(False)
    while True:
        if len(buffer) >= total_data_count * 8: break
        buffer.put(PAD0, 8)
        if len(buffer) >= total_data_count * 8: break
        buffer.put(PAD1, 8)
    return create_bytes(buffer, rs_b)

class Poly:
    def __init__(self, num, shift):
        offset = 0
        while offset < len(num) and num[offset] == 0: offset += 1
        self.num = [0] * (len(num) - offset + shift)
        for i in range(len(num) - offset): self.num[i] = num[i + offset]
    def __getitem__(self, index):
        return self.num[index]
    def __len__(self): return len(self.num)
    def __mul__(self, e):
        num = [0] * (len(self) + len(e) - 1)
        for i in range(len(self)):
            for j in range(len(e)): num[i + j] ^= TEXP[(TLOG[self[i]] + TLOG[e[j]]) % 255]
        return Poly(num, 0)
    def __mod__(self, e):
        if len(self) - len(e) < 0: return self
        ratio, num = TLOG[self[0]] - TLOG[e[0]], [0] * len(self)
        for i in range(len(self)): num[i] = self[i]
        for i in range(len(e)): num[i] ^= TEXP[(TLOG[e[i]] + ratio) % 255]
        return Poly(num, 0) % e

class RSBlock:
    def __init__(self, total_c, data_c):
        self.total_count, self.data_count = total_c, data_c

def rs_blocks(version, error_correction):
    offset = RS_BLOCK_OFFSET[error_correction]
    rs_b, blocks = RS_BLOCK_TABLE[(version - 1) * 4 + offset], []
    for i in range(0, len(rs_b), 3):
        count, total_count, data_count = rs_b[i:i + 3]
        for j in range(count): blocks.append(RSBlock(total_count, data_count))
    return blocks

class QRCode:
    def __init__(self, data='hello', error_co=0):
        self.version, self.error_co, size, self.m, self.m_count, self.data_cache, self.data_list = None, int(error_co), 1, None, 0, None, []
        self.data_list.append(QRData(data))
        while True:
            try: self.data_cache = create_data(size, self.error_co, self.data_list)
            except: size += 1
            else:
                self.version = size
                break
        self.makeImpl(False, self.best_mask_pattern())

    def makeImpl(self, test, mask_pattern):
        self.m_count = self.version * 4 + 17
        self.m = [None] * self.m_count
        for row in range(self.m_count):
            self.m[row] = [None] * self.m_count
            for col in range(self.m_count): self.m[row][col] = None   
        self.setup_position_probe_pattern(0, 0)
        self.setup_position_probe_pattern(self.m_count - 7, 0)
        self.setup_position_probe_pattern(0, self.m_count - 7)
        self.setup_position_adjust_pattern()
        self.setup_timing_pattern()
        self.setup_type_info(test, mask_pattern)
        if self.version >= 7: self.setup_type_number(test)
        if self.data_cache is None: self.data_cache = create_data(self.version, self.error_co, self.data_list)
        self.map_data(self.data_cache, mask_pattern)

    def setup_position_probe_pattern(self, row, col):
        for r in range(-1, 8):
            if row + r <= -1 or self.m_count <= row + r: continue
            for c in range(-1, 8):
                if col + c <= -1 or self.m_count <= col + c: continue
                self.m[row + r][col + c] = True if (0 <= r and r <= 6 and (c == 0 or c == 6) or (0 <= c and c <= 6 and (r == 0 or r == 6)) or (2 <= r and r <= 4 and 2 <= c and c <= 4)) else False

    def best_mask_pattern(self):
        min_lost_point, pattern = 0, 0
        for i in range(8):
            self.makeImpl(True, i)
            lost_point = lost_point1(self.m)
            if i == 0 or min_lost_point > lost_point: min_lost_point, pattern = lost_point, i
        return pattern

    def svg(self, ox=0, oy=0, d=2, txt=''):
        o, mc = '', self.m_count
        for r in range(mc):
            k = 0
            for c in range(mc):
                if self.m[r][c]: k += 1
                elif k > 0:
                    o += '<rect x="%d" y="%d" width="%d" height="%d"/>\n' % (ox+(c-k)*d, oy+r*d, k*d, d)
                    k = 0
            if k > 0: o += '<rect x="%d" y="%d" width="%d" height="%d"/>\n' % (ox+(mc-k)*d, oy+r*d, k*d, d)
        o += '<ellipse cx="%s" cy="%s" rx="180" ry="230" style="fill:none;stroke:grey;"/>' % (ox+104, oy+100)
        o += '<g transform="translate(%s,%s)rotate(-90)"><text font-family="courier" font-size="24">%s</text></g>' % (ox-26, oy+190, txt)
        
        o += '<g transform="translate(%s,%s)scale(.3,.3)"><path d="m 351.08819,136.64085 c 0.646,-4.388 0.991,-8.874 0.991,-13.441 0,-50.615002 -41.033,-91.648002 -91.648,-91.648002 -33.429,0 -62.667,17.904 -78.676,44.641 -4.878,-1.726 -10.125,-2.674 -15.594,-2.674 -23.393,0 -42.772,17.183 -46.208,39.614002 -1.252,-0.071 -2.513,-0.115 -3.783,-0.115 -36.553997,0 -66.190001,29.636 -66.190001,66.191 0,34.771 26.821004,63.262 60.898001,65.961 6.842,14.367 21.493,24.298 38.464,24.298 18.309,0 33.916,-11.557 39.933,-27.771 l 31.347,0 c 15.187,-16.669 27.964,-31.646 28.929,-53.199 l -31.379,0 c -6.42,0 -12.837,-6.421 -12.837,-12.842 l 0,-51.013 c 0,-6.247 6.417,-12.665 12.837,-12.665 l 6.941,0 0,-37.654002 0.148,0 c -0.076,-0.512 -0.148,-1.024 -0.148,-1.562 0,-5.553 4.164,-9.89 9.715,-9.89 5.556,0 9.894,4.337 9.894,9.89 0,0.538 -0.076,1.05 -0.153,1.562 l 0.153,0 0,37.654002 24.639,0 0,-37.654002 0.153,0 c -0.078,-0.511 -0.153,-1.022 -0.153,-1.562 0,-5.553 4.337,-9.89 9.89,-9.89 5.551,0 9.716,4.337 9.716,9.89 0,0.54 -0.072,1.051 -0.148,1.562 l 0.148,0 0,37.654002 6.941,0 c 6.421,0 12.837,6.418 12.837,12.665 l 0,51.013 c 0,6.42 -6.417,12.842 -12.837,12.842 l -26.712,0 c -0.727,22.061 -10.49,38.518 -22.497,53.199 l 0.028,0 c 6.017,16.215 21.624,27.771 39.933,27.771 18.009,0 33.398,-11.187 39.623,-26.985 1.235,0.082 2.477,0.14 3.733,0.14 30.419,0 55.082,-24.663 55.082,-55.082 -10e-4,-22.957 -14.047,-42.624 -34.01,-50.9 z" /></g>' % (ox+40, oy-110)

        o += '<g transform="translate(%s,%s)scale(.48,.48)"><path d="m 59.022451,301.71112 0,1.187 c 1.843,-2.271 3.754,-3.938 5.739,-5.005 1.985,-1.065 4.232004,-1.595 6.744004,-1.595 3.01,0 5.788,0.773 8.321,2.329 2.533,1.555 4.538,3.827 6.008,6.816 1.472,2.99 2.208,6.53 2.208,10.617 0,3.014 -0.425,5.784 -1.275,8.303 -0.848,2.525 -2.016,4.641 -3.497,6.35 -1.483,1.711 -3.235,3.025 -5.254,3.945 -2.019,0.92 -4.191,1.38 -6.511,1.38 -2.797,0 -5.148004,-0.562 -7.048004,-1.682 -1.902,-1.125 -3.712,-2.775 -5.436,-4.951 l 0,14.706 c 0,4.303 -1.564,6.456 -4.697,6.456 -1.844,0 -3.061,-0.555 -3.658,-1.669 -0.599,-1.111 -0.898,-2.731 -0.898,-4.858 l 0,-42.257 c 0,-1.862 0.405,-3.254 1.218,-4.178 0.814,-0.917 1.926,-1.38 3.338,-1.38 1.387,0 2.517,0.47 3.389,1.418 0.874,0.944 1.309,2.3 1.309,4.068 z m 19.192004,14.241 c 0,-2.582 -0.398,-4.799 -1.185,-6.654 -0.788,-1.852 -1.882,-3.274 -3.282,-4.266 -1.399,-0.994 -2.945,-1.489 -4.646,-1.489 -2.702004,0 -4.978004,1.062 -6.831004,3.191 -1.852,2.13 -2.779,5.262 -2.779,9.398 0,3.897 0.918,6.929 2.757,9.093 1.845,2.166 4.128,3.247 6.853004,3.247 1.625,0 3.135,-0.472 4.52,-1.417 1.387,-0.946 2.5,-2.361 3.336,-4.249 0.837,-1.891 1.257,-4.174 1.257,-6.854 z m 17.609,14.134 0,-42.471 c 0,-1.96 0.438,-3.441 1.309,-4.447 0.873,-1.003 2.051997,-1.505 3.532995,-1.505 1.485,0 2.68,0.495 3.587,1.488 0.91,0.991 1.365,2.479 1.365,4.464 l 0,42.471 c 0,1.985 -0.463,3.475 -1.381,4.466 -0.924,0.992 -2.112,1.486 -3.571,1.486 -1.435998,0 -2.599995,-0.512 -3.494995,-1.543 -0.896,-1.027 -1.347,-2.496 -1.347,-4.409 z m 45.266995,0.429 0,-1.257 c -1.173,1.486 -2.405,2.73 -3.696,3.732 -1.292,1.004 -2.701,1.75 -4.232,2.244 -1.53,0.488 -3.276,0.733 -5.234,0.733 -2.367,0 -4.493,-0.493 -6.368,-1.474 -1.879,-0.978 -3.33099,-2.328 -4.357,-4.052 -1.223,-2.077 -1.83,-5.067 -1.83,-8.968 l 0,-19.402 c 0,-1.96 0.441,-3.425 1.327,-4.395 0.88401,-0.969 2.05801,-1.453 3.513,-1.453 1.482,0 2.68,0.492 3.589,1.468 0.908,0.984 1.363,2.441 1.363,4.38 l 0,15.676 c 0,2.271 0.192,4.177 0.573,5.721 0.382,1.541 1.07,2.748 2.063,3.622 0.993,0.871 2.336,1.309 4.036,1.309 1.649,0 3.204,-0.492 4.662,-1.47 1.459,-0.983 2.522,-2.262 3.193,-3.841 0.55,-1.385 0.825,-4.423 0.825,-9.11 l 0,-11.906 c 0,-1.938 0.454,-3.396 1.361,-4.38 0.911,-0.976 2.094,-1.468 3.553,-1.468 1.458,0 2.629,0.484 3.517,1.453 0.882,0.97 1.327,2.435 1.327,4.395 l 0,28.37 c 0,1.866 -0.427,3.266 -1.273,4.198 -0.852,0.934 -1.946,1.396 -3.284,1.396 -1.34,0 -2.444,-0.481 -3.318,-1.45 -0.876,-0.968 -1.31,-2.324 -1.31,-4.071 z m 54.95,-27.115 0,28.442 c 0,3.253 -0.347,6.05 -1.04,8.394 -0.694,2.341 -1.805,4.279 -3.336,5.812 -1.532,1.529 -3.533,2.666 -6.008,3.406 -2.476,0.743 -5.556,1.113 -9.238,1.113 -3.368,0 -6.384,-0.476 -9.037,-1.417 -2.654,-0.942 -4.699,-2.165 -6.135,-3.66 -1.436,-1.493 -2.152,-3.03 -2.152,-4.608 0,-1.195 0.405,-2.17 1.221,-2.924 0.812,-0.752 1.792,-1.127 2.941,-1.127 1.434,0 2.69,0.63 3.767,1.897 0.524,0.647 1.07,1.298 1.631,1.956 0.562,0.656 1.186,1.221 1.866,1.686 0.682,0.468 1.499,0.813 2.458,1.043 0.953,0.226 2.058,0.34 3.301,0.34 2.531,0 4.497,-0.354 5.9,-1.058 1.396,-0.709 2.377,-1.694 2.94,-2.96 0.561,-1.27 0.888,-2.625 0.985,-4.072 0.094,-1.446 0.167,-3.773 0.215,-6.974 -1.504,2.102 -3.248,3.705 -5.218,4.803 -1.976,1.101 -4.321,1.65 -7.048,1.65 -3.276,0 -6.14,-0.837 -8.592,-2.51 -2.45,-1.674 -4.334,-4.019 -5.65,-7.031 -1.315,-3.011 -1.971,-6.493 -1.971,-10.437 0,-2.941 0.4,-5.596 1.201,-7.965 0.803,-2.366 1.946,-4.364 3.426,-5.99 1.483,-1.625 3.195,-2.851 5.13,-3.676 1.936,-0.824 4.064,-1.236 6.386,-1.236 2.772,0 5.177,0.529 7.209,1.595 2.03,1.066 3.922,2.733 5.667,5.005 l 0,-1.327 c 0,-1.7 0.418,-3.013 1.257,-3.945 0.835,-0.933 1.911,-1.399 3.227,-1.399 1.888,0 3.145,0.614 3.765,1.846 0.62,1.23 0.932,3.008 0.932,5.328 z m -28.373,12.41 c 0,3.969 0.868,6.969 2.602,9.003 1.732,2.032 3.973,3.05 6.727,3.05 1.625,0 3.16,-0.439 4.608,-1.311 1.443,-0.875 2.624,-2.189 3.535,-3.945 0.908,-1.76 1.361,-3.893 1.361,-6.402 0,-3.994 -0.88,-7.103 -2.638,-9.326 -1.753,-2.224 -4.072,-3.336 -6.941,-3.336 -2.797,0 -5.038,1.062 -6.725,3.191 -1.686,2.13 -2.529,5.152 -2.529,9.076 z m 72.45,-12.41 0,28.442 c 0,3.253 -0.346,6.05 -1.04,8.394 -0.696,2.341 -1.806,4.279 -3.337,5.812 -1.528,1.529 -3.533,2.666 -6.006,3.406 -2.476,0.743 -5.555,1.113 -9.238,1.113 -3.372,0 -6.382,-0.476 -9.037,-1.417 -2.656,-0.942 -4.701,-2.165 -6.135,-3.66 -1.436,-1.493 -2.154,-3.03 -2.154,-4.608 0,-1.195 0.407,-2.17 1.221,-2.924 0.812,-0.752 1.792,-1.127 2.94,-1.127 1.434,0 2.69,0.63 3.768,1.897 0.526,0.647 1.068,1.298 1.633,1.956 0.559,0.656 1.181,1.221 1.862,1.686 0.682,0.468 1.502,0.813 2.457,1.043 0.958,0.226 2.056,0.34 3.3,0.34 2.537,0 4.504,-0.354 5.901,-1.058 1.4,-0.709 2.379,-1.694 2.942,-2.96 0.562,-1.27 0.892,-2.625 0.987,-4.072 0.094,-1.446 0.166,-3.773 0.215,-6.974 -1.509,2.102 -3.245,3.705 -5.22,4.803 -1.973,1.101 -4.325,1.65 -7.048,1.65 -3.276,0 -6.14,-0.837 -8.588,-2.51 -2.456,-1.674 -4.337,-4.019 -5.652,-7.031 -1.316,-3.011 -1.974,-6.493 -1.974,-10.437 0,-2.941 0.405,-5.596 1.204,-7.965 0.799,-2.366 1.942,-4.364 3.424,-5.99 1.483,-1.625 3.193,-2.851 5.13,-3.676 1.938,-0.824 4.066,-1.236 6.384,-1.236 2.773,0 5.176,0.529 7.209,1.595 2.034,1.066 3.921,2.733 5.667,5.005 l 0,-1.327 c 0,-1.7 0.421,-3.013 1.254,-3.945 0.839,-0.933 1.917,-1.399 3.229,-1.399 1.891,0 3.146,0.614 3.768,1.846 0.622,1.232 0.934,3.008 0.934,5.328 z m -28.371,12.41 c 0,3.969 0.863,6.969 2.597,9.003 1.734,2.032 3.978,3.05 6.726,3.05 1.627,0 3.164,-0.439 4.609,-1.311 1.448,-0.875 2.625,-2.189 3.533,-3.945 0.91,-1.76 1.363,-3.893 1.363,-6.402 0,-3.994 -0.876,-7.103 -2.636,-9.326 -1.757,-2.224 -4.07,-3.336 -6.939,-3.336 -2.799,0 -5.039,1.062 -6.724,3.191 -1.688,2.13 -2.529,5.152 -2.529,9.076 z m 37.314,14.276 0,-42.471 c 0,-1.96 0.436,-3.441 1.311,-4.447 0.874,-1.003 2.047,-1.505 3.533,-1.505 1.484,0 2.678,0.495 3.587,1.488 0.908,0.991 1.362,2.479 1.362,4.464 l 0,42.471 c 0,1.985 -0.459,3.475 -1.38,4.466 -0.92,0.992 -2.112,1.486 -3.569,1.486 -1.434,0 -2.6,-0.512 -3.499,-1.543 -0.895,-1.027 -1.345,-2.496 -1.345,-4.409 z m 47.167,-11.551 -19.155,0 c 0.025,2.226 0.474,4.185 1.346,5.882 0.873,1.7 2.036,2.979 3.48,3.839 1.446,0.862 3.043,1.291 4.79,1.291 1.168,0 2.24,-0.138 3.209,-0.41 0.969,-0.279 1.905,-0.707 2.815,-1.291 0.91,-0.588 1.745,-1.216 2.511,-1.886 0.767,-0.67 1.758,-1.577 2.977,-2.726 0.502,-0.428 1.222,-0.644 2.151,-0.644 1.005,0 1.817,0.273 2.441,0.823 0.62,0.55 0.931,1.329 0.931,2.332 0,0.884 -0.345,1.917 -1.038,3.104 -0.696,1.181 -1.743,2.316 -3.141,3.406 -1.4,1.087 -3.155,1.991 -5.271,2.709 -2.119,0.716 -4.553,1.072 -7.301,1.072 -6.291,0 -11.18,-1.79 -14.669,-5.378 -3.493,-3.589 -5.24,-8.452 -5.24,-14.6 0,-2.894 0.432,-5.576 1.292,-8.054 0.859,-2.474 2.116,-4.596 3.767,-6.364 1.649,-1.772 3.681,-3.128 6.099,-4.072 2.414,-0.945 5.091,-1.417 8.033,-1.417 3.826,0 7.107,0.807 9.847,2.423 2.736,1.612 4.788,3.699 6.153,6.258 1.363,2.559 2.043,5.165 2.043,7.819 0,2.463 -0.705,4.058 -2.117,4.788 -1.409,0.733 -3.392,1.096 -5.953,1.096 z m -19.155,-5.56 17.757,0 c -0.24,-3.349 -1.145,-5.853 -2.71,-7.515 -1.563,-1.663 -3.627,-2.493 -6.187,-2.493 -2.438,0 -4.439,0.845 -6.006,2.529 -1.568,1.688 -2.517,4.18 -2.854,7.479 z m 38.352,23.063 c -1.484,0 -2.765,-0.476 -3.837,-1.435 -1.078,-0.954 -1.616,-2.294 -1.616,-4.017 0,-1.46 0.514,-2.713 1.544,-3.763 1.025,-1.055 2.294,-1.581 3.803,-1.581 1.504,0 2.79,0.522 3.854,1.559 1.063,1.044 1.597,2.304 1.597,3.785 0,1.701 -0.533,3.031 -1.597,4.001 -1.065,0.969 -2.315,1.451 -3.748,1.451 z m 10.722,-35.438 c 0,-2.343 1.638,-3.515 4.916,-3.515 l 2.331,0 0,-2.939 c 0,-3.063 0.387,-5.493 1.166,-7.302 0.776,-1.803 2.092,-3.119 3.947,-3.945 1.854,-0.824 4.394,-1.236 7.619,-1.236 5.717,0 8.574,1.397 8.574,4.195 0,0.908 -0.298,1.688 -0.897,2.332 -0.599,0.644 -1.305,0.969 -2.117,0.969 -0.383,0 -1.04,-0.072 -1.973,-0.217 -0.933,-0.143 -1.721,-0.215 -2.367,-0.215 -1.77,0 -2.904,0.522 -3.407,1.561 -0.502,1.043 -0.754,2.529 -0.754,4.468 l 0,2.33 2.403,0 c 3.73,0 5.595,1.123 5.595,3.372 0,1.603 -0.496,2.618 -1.488,3.051 -0.991,0.43 -2.361,0.646 -4.106,0.646 l -2.403,0 0,25.932 c 0,1.937 -0.459,3.411 -1.379,4.433 -0.924,1.013 -2.112,1.52 -3.571,1.52 -1.387,0 -2.541,-0.507 -3.461,-1.52 -0.92,-1.021 -1.381,-2.496 -1.381,-4.433 l 0,-25.932 -2.69,0 c -1.459,0 -2.582,-0.331 -3.369,-0.987 -0.794,-0.661 -1.188,-1.515 -1.188,-2.568 l 0,0 z m 39.886,21.307 0,8.179 c 0,1.985 -0.466,3.475 -1.399,4.466 -0.933,0.992 -2.116,1.486 -3.551,1.486 -1.41,0 -2.569,-0.501 -3.477,-1.503 -0.911,-1.005 -1.365,-2.488 -1.365,-4.449 l 0,-27.261 c 0,-4.401 1.587,-6.6 4.773,-6.6 1.624,0 2.795,0.514 3.513,1.54 0.72,1.031 1.112,2.55 1.183,4.557 1.172,-2.007 2.374,-3.525 3.605,-4.557 1.231,-1.026 2.875,-1.54 4.932,-1.54 2.056,0 4.054,0.514 5.99,1.54 1.938,1.031 2.906,2.395 2.906,4.09 0,1.195 -0.412,2.183 -1.239,2.962 -0.822,0.774 -1.716,1.164 -2.67,1.164 -0.358,0 -1.228,-0.222 -2.602,-0.661 -1.375,-0.445 -2.589,-0.665 -3.64,-0.665 -1.436,0 -2.607,0.377 -3.515,1.128 -0.911,0.756 -1.616,1.873 -2.115,3.354 -0.503,1.484 -0.852,3.246 -1.043,5.293 -0.19,2.042 -0.286,4.536 -0.286,7.477 z"/></g>' % (ox+4, oy+108)
        return o + '\n'

    def pdf(self, ox=0, oy=0, d=10, size=False, color = b'0 0 0'):
        o, mc = color + b' rg ', self.m_count
        if size:
            o += bytes('q .9 .9 .9 rg BT 1 0 0 1 2 2 Tm /F1 3 Tf (%d) Tj ET Q ' % self.m_count, 'ascii')
        for r in range(mc):
            k = 0
            for c in range(mc):
                if self.m[r][c]: k += 1
                elif k > 0:
                    o += bytes('%d %d %d %d re ' % (ox+(c-k)*d, oy-r*d, k*d, d), 'ascii')
                    k = 0
            if k > 0: o += bytes('%d %d %d %d re ' % (ox+(mc-k)*d, oy-r*d, k*d, d), 'ascii')
        return o + b'f '

    def setup_timing_pattern(self):
        for r in range(8, self.m_count - 8):
            if self.m[r][6] != None: continue
            self.m[r][6] = (r % 2 == 0)
        for c in range(8, self.m_count - 8):
            if self.m[6][c] != None: continue
            self.m[6][c] = (c % 2 == 0)

    def setup_position_adjust_pattern(self):
        pos = pattern_position(self.version)
        for i in range(len(pos)):
            for j in range(len(pos)):
                row, col = pos[i], pos[j]
                if self.m[row][col] != None: continue
                for r in range(-2, 3):
                    for c in range(-2, 3):
                        self.m[row + r][col + c] = True if (r == -2 or r == 2 or c == -2 or c == 2 or (r == 0 and c == 0)) else False

    def setup_type_number(self, test):
        bits = BCH_type_number(self.version)
        for i in range(18): self.m[i // 3][i % 3 + self.m_count - 8 - 3] = (not test and ((bits >> i) & 1) == 1)
        for i in range(18): self.m[i % 3 + self.m_count - 8 - 3][i // 3] = (not test and ((bits >> i) & 1) == 1)

    def setup_type_info(self, test, mask_pattern):
        bits = BCH_type_info((self.error_co << 3) | mask_pattern)
        for i in range(15): 
            mod = (not test and ((bits >> i) & 1) == 1)
            if i < 6: self.m[i][8] = mod
            elif i < 8: self.m[i + 1][8] = mod
            else: self.m[self.m_count - 15 + i][8] = mod
        for i in range(15): 
            mod = (not test and ((bits >> i) & 1) == 1)
            if i < 8: self.m[8][self.m_count - i - 1] = mod
            elif i < 9: self.m[8][15 - i - 1 + 1] = mod
            else: self.m[8][15 - i - 1] = mod
        self.m[self.m_count - 8][8] = (not test) 

    def map_data(self, data, mask_pattern):
        inc, row, bitIndex, byteIndex, mask_func1 = -1, self.m_count - 1, 7, 0, mask_func(mask_pattern)
        for col in range(self.m_count - 1, 0, -2):
            if col == 6: col -= 1
            while True:
                for c in range(2):
                    if self.m[row][col - c] == None:
                        dark = False
                        if byteIndex < len(data): dark = (((data[byteIndex] >> bitIndex) & 1) == 1)
                        if mask_func1(row, col - c): dark = not dark
                        self.m[row][col - c] = dark
                        bitIndex -= 1
                        if bitIndex == -1:
                            byteIndex += 1
                            bitIndex = 7
                row += inc
                if row < 0 or self.m_count <= row:
                    row -= inc
                    inc = -inc
                    break

##### Web app #####
def app_update():
    "_"
    cd = 'cd %s; git pull origin' % os.path.dirname(os.path.abspath(__file__))
    out, err = subprocess.Popen((cd), shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).communicate()
    return '%s\n' % err.decode('utf8') if err else 'Message:%s\n' % out.decode('utf8')

def application(environ, start_response):
    ""
    mime, o, now, fname, port = 'text/plain; charset=utf8', 'Error:', '%s' % datetime.datetime.now(), 'default.txt', environ['SERVER_PORT']
    (raw, way) = (environ['wsgi.input'].read(), 'post') if environ['REQUEST_METHOD'].lower() == 'post' else (urllib.parse.unquote(environ['QUERY_STRING']), 'get')
    base = environ['PATH_INFO'][1:]
    if way == 'post':
        o = 'post'
    else: # get
        if base == '' and raw == '_update': 
            o = app_update()
        else:
            o, mime = display(), 'image/svg+xml'
    start_response('200 OK', [('Content-type', mime)])
    return [o if mime in ('application/pdf', 'image/png', 'image/svg+xml', 'image/jpg') else o.encode('utf8')] 


def display():
    qrs = 201503190000
    o, k, nx, ny = '<svg %s width="1940" height="4760">\n' % _SVGNS, 0, 5, 10
    for j in range(ny):
        for i in range(nx):
            k += 1
            s = '%d' % (qrs+k)
            o += QRCode(s, 2).svg(100+380*i, 150+470*j, 10, s) 
    return o + '</svg>\n'

if __name__ == '__main__':
    print (display())

# End ⊔net!
