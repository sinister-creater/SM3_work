import struct
import sys
import time


# --- 模块 1/2/3: 核心算法实现 ---
class SM3:
    """
    SM3 密码杂凑算法核心实现
    严格遵循 GM/T 0004-2012 / GB/T 32905-2016 规范定义的逻辑结构。
    """

    def __init__(self):
        # 模块 3: 初始值设置 - 链接变量 IV
        # 7380166f, 4914b2b9, 172442d7, da8a0600, a96f30bc, 163138aa, e38dee4d, b0fb0e4e
        self.initial_vector = [
            0x7380166f, 0x4914b2b9, 0x172442d7, 0xda8a0600,
            0xa96f30bc, 0x163138aa, 0xe38dee4d, 0xb0fb0e4e
        ]
        # 模块 3: 常量 T_j
        self.T_0_to_15 = 0x79cc4519
        self.T_16_to_63 = 0x7a879d8a
        # 模 2^32 掩码
        self.MASK = 0xFFFFFFFF

    @staticmethod
    def circular_shift(value, bits):
        """
        执行循环左移操作 X <<< bits，并进行 32 位截断。
        bits 自动取模 32 (即实现了 X <<< (bits mod 32))
        """
        bits = bits % 32
        return ((value << bits) | (value >> (32 - bits))) & 0xFFFFFFFF

    # --- 模块 3: 布尔函数 FF/GG ---
    @staticmethod
    def bool_func_ff(x_val, y_val, z_val, round_num):
        """FF 布尔函数 (FF_1 和 FF_2)"""
        if 0 <= round_num <= 15:
            # 1-16 轮 (FF_1): X XOR Y XOR Z
            return x_val ^ y_val ^ z_val
        else:
            # 17-64 轮 (FF_2): (X AND Y) OR (X AND Z) OR (Y AND Z)
            return (x_val & y_val) | (x_val & z_val) | (y_val & z_val)

    @staticmethod
    def bool_func_gg(x_val, y_val, z_val, round_num):
        """GG 布尔函数 (GG_1 和 GG_2)"""
        if 0 <= round_num <= 15:
            # 1-16 轮 (GG_1): X XOR Y XOR Z
            return x_val ^ y_val ^ z_val
        else:
            # 17-64 轮 (GG_2): (X AND Y) OR ((NOT X) AND Z)
            not_x_val = 0xFFFFFFFF ^ x_val
            return (x_val & y_val) | ((0xFFFFFFFF ^ x_val) & z_val)

    # --- 模块 3: 置换函数 P0 ---
    @staticmethod
    def permutation_p0(x_val):
        """P0 置换函数 P_0(X) = X XOR (X <<< 9) XOR (X <<< 17)"""
        return (x_val ^ SM3.circular_shift(x_val, 9) ^ SM3.circular_shift(x_val, 17)) & 0xFFFFFFFF

    # --- 模块 2: 置换函数 P1 ---
    @staticmethod
    def permutation_p1(x_val):
        """P1 置换函数 P_1(X) = X XOR (X <<< 15) XOR (X <<< 23)"""
        return (x_val ^ SM3.circular_shift(x_val, 15) ^ SM3.circular_shift(x_val, 23)) & 0xFFFFFFFF

    # --- 模块 1: 消息填充模块 ---
    def prepare_data(self, input_data):
        """
        数据预处理/消息填充函数。
        严格遵循标准：补 '1'，补 '0' 直到长度 ≡ 448 mod 512，最后补 64bit 原始长度 l。
        """
        # 1. 输入处理：转换为字节流
        if isinstance(input_data, str):
            # 尝试 UTF-8 编码，失败则尝试 GBK
            try:
                input_data = input_data.encode('utf-8')
            except UnicodeEncodeError:
                try:
                    input_data = input_data.encode('gbk')
                except Exception:
                    raise ValueError("无法将输入字符串编码为 UTF-8 或 GBK 字节流")

        # 原始消息长度 l (单位: bit)
        original_length = len(input_data) * 8

        # 2. 填充规则：添加比特 '1' (即 b'\x80')
        input_data += b'\x80'

        # 3. 填充规则：添加 k 个 '0'
        # 目标: len(input_data) * 8 ≡ 448 (mod 512), 即 len(input_data) % 64 ≡ 56
        # 确保涵盖 l ≡ 448 mod 512 和 l ≡ 0 mod 512 的特殊场景
        while (len(input_data) % 64) != 56:
            input_data += b'\x00'

        # 4. 填充规则：最后补 64bit 的 l (大端序)
        # >Q 表示大端序 unsigned long long (8 bytes)
        input_data += struct.pack('>Q', original_length)

        # 模块 2 断言判断
        assert len(input_data) % 64 == 0, "填充后的消息长度不是 512 bit 的整数倍"

        return input_data

    # --- 模块 2: 分组处理模块 ---
    def expand_data_block(self, block):
        """分组扩展，生成 W (W_0-W_67) 和 W' (W'_0-W'_63) 字序列"""
        word_list = [0] * 68
        derived_list = [0] * 64

        # a) W_j = B_i的第j个 32bit 字 (j=0-15)
        for i in range(16):
            # 大端序解析 32bit 字
            word_list[i] = struct.unpack('>I', block[i * 4:(i + 1) * 4])[0]

        # b) 计算 W16...W67 (所有操作均为模 2^32 运算)
        for i in range(16, 68):
            # W_{j-3} <<< 15
            term1 = self.circular_shift(word_list[i - 3], 15)
            # P_1 的输入项: W_{j-16} XOR W_{j-9} XOR term1
            p1_input = word_list[i - 16] ^ word_list[i - 9] ^ term1

            # P_1(...)
            temp_val = self.permutation_p1(p1_input)

            # W_j = P_1(...) XOR (W_{j-13} <<< 7) XOR W_{j-6}
            temp_val ^= self.circular_shift(word_list[i - 13], 7)
            temp_val ^= word_list[i - 6]

            word_list[i] = temp_val & self.MASK

        # c) W'_j = W_j XOR W_{j+4} (j=0-63)
        for i in range(64):
            derived_list[i] = word_list[i] ^ word_list[i + 4]

        return word_list, derived_list

    # --- 模块 3: 压缩函数模块 ---
    def compression_step(self, state_vector, words, derived_words):
        """压缩函数核心步骤 (64 轮迭代)"""
        # 载入工作变量 A-H
        a, b, c, d, e, f, g, h = state_vector
        MASK = self.MASK

        for round_idx in range(64):
            # 1. 确定常量 T_j
            constant = self.T_0_to_15 if round_idx < 16 else self.T_16_to_63

            # T_j <<< (j mod 32)
            # circular_shift 内部已进行 mod 32 运算，符合最新要求
            tj_shifted = self.circular_shift(constant, round_idx)

            # 2. SS1 计算 (模 2^32 加法)
            # SS1 = ((A <<< 12) + E + (T_j <<< (j mod 32))) <<< 7
            temp_a_shifted = self.circular_shift(a, 12)
            ss1_input = (temp_a_shifted + e + tj_shifted) & MASK
            ss1 = self.circular_shift(ss1_input, 7)

            # 3. SS2 计算
            # SS2 = SS1 XOR (A <<< 12)
            ss2 = ss1 ^ temp_a_shifted

            # 4. TT1 计算 (模 2^32 加法)
            # TT1 = FF(A,B,C) + D + SS2 + W'_j
            ff_result = self.bool_func_ff(a, b, c, round_idx)
            tt1 = (ff_result + d + ss2 + derived_words[round_idx]) & MASK

            # 5. TT2 计算 (模 2^32 加法)
            # TT2 = GG(E,F,G) + H + SS1 + W_j
            gg_result = self.bool_func_gg(e, f, g, round_idx)
            tt2 = (gg_result + h + ss1 + words[round_idx]) & MASK

            # 6. 变量更新 (并行更新)
            # 存储旧值，实现并行赋值，避免顺序依赖错误
            a_new = tt1
            b_new = a
            c_new = self.circular_shift(b, 9)
            d_new = c
            e_new = self.permutation_p0(tt2)  # E = P_0(TT2)
            f_new = e
            g_new = self.circular_shift(f, 19)  # G = F <<< 19
            h_new = g

            # 并行赋值
            a, b, c, d = a_new, b_new, c_new, d_new
            e, f, g, h = e_new, f_new, g_new, h_new

        # 结果输出: A,B,C,D,E,F,G,H 与初始 IV 对应异或，得到新的 IV
        result = [
            a ^ state_vector[0], b ^ state_vector[1], c ^ state_vector[2], d ^ state_vector[3],
            e ^ state_vector[4], f ^ state_vector[5], g ^ state_vector[6], h ^ state_vector[7]
        ]

        return result

    # --- 模块 4: 函数接口 ---
    def sm3_hash(self, input_data: bytes) -> str:
        """
        核心哈希函数接口
        :param input_data: 待哈希的字节流 (bytes)
        :return: 64 位十六进制 SM3 哈希值 (str)
        """
        # 1. 消息填充
        processed_data = self.prepare_data(input_data)
        current_state = self.initial_vector.copy()

        # 2. 迭代压缩
        block_count = len(processed_data) // 64

        for i in range(block_count):
            block = processed_data[i * 64:(i + 1) * 64]
            # 分组扩展
            words, derived_words = self.expand_data_block(block)
            # 压缩函数迭代
            current_state = self.compression_step(current_state, words, derived_words)

        # 3. 结果输出
        # 将最终 IV 按顺序拼接，转换为 64 位十六进制字符串 (UTF-8 编码)
        hash_result = ''.join(f'{word:08x}' for word in current_state)
        return hash_result

    def calculate_file_hash(self, file_path):
        """计算文件杂凑值 (处理文件访问错误)"""
        try:
            # 读取文件字节流
            with open(file_path, 'rb') as file:
                file_content = file.read()
            return self.sm3_hash(file_content)
        except FileNotFoundError:
            print(f"错误：找不到文件 '{file_path}'")
            return None
        except PermissionError:
            print(f"错误：没有权限访问文件 '{file_path}'")
            return None
        except Exception as error:
            print(f"处理文件时出错：{error}")
            return None


# --- 模块 4: 工具化封装 (命令行工具) ---
def process_command_line():
    """
    处理命令行参数，适配 -s (字符串) 和 -f (文件) 参数格式。
    """

    # 查找参数
    arg_type = None
    arg_value = None

    # 查找 -s 或 -f 参数及其后的值
    if len(sys.argv) > 2:
        if sys.argv[1] == '-s':
            arg_type = 'string'
            arg_value = sys.argv[2]
        elif sys.argv[1] == '-f':
            arg_type = 'file'
            arg_value = sys.argv[2]

    if arg_type is None:
        print("使用说明 (命令行工具):")
        print("计算字符串哈希: python sm3_tool.py -s \"输入字符串\"")
        print("计算文件哈希: python sm3_tool.py -f 文件名/路径")
        print("注意: 使用uv时，'python' 可能需要替换为 'uv run'")
        return

    sm3_calculator = SM3()

    if arg_type == 'string':
        # 字符串输入 (示例：./sm3_tool -s "abc")
        start_time = time.time()
        # 传入字符串，让 sm3_hash 内部处理编码
        result = sm3_calculator.sm3_hash(arg_value)
        end_time = time.time()
        if result:
            print(f"输入内容: {arg_value}")
            print(f"哈希结果: {result}")
            print(f"计算时间: {(end_time - start_time) * 1000:.2f}毫秒")

    elif arg_type == 'file':
        # 文件输入 (示例：python sm3_tool.py -f test.txt)
        filename = arg_value
        start_time = time.time()
        result = sm3_calculator.calculate_file_hash(filename)
        end_time = time.time()
        if result:
            print(f"文件路径: {filename}")
            print(f"哈希结果: {result}")
            print(f"计算时间: {(end_time - start_time) * 1000:.2f}毫秒")


if __name__ == "__main__":
    process_command_line()
