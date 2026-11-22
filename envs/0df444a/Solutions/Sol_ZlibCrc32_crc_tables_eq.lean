-- Prove2me | solution 1 for ZlibCrc32.crc_tables_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T10:24:49.171342+00:00
-- url     : https://prove2.me/submissions/417c4bee-87cf-4f45-a7c1-d0ca7ed28350

import Definitions.Def_ZlibCrc32_Spec
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Nat.Bitwise

open Polynomial KadatchJenkins ZlibCrc32

namespace ZlibCrc32Tables

/-- The polynomial of the low `D` bits of `n`, register convention: bit `i` is the coefficient
of `x^(D-1-i)`. -/
noncomputable def natPoly (n D : ℕ) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range D, if n.testBit i then X ^ (D - 1 - i) else 0

/-- Multiplication by `x` mod `P` on a reflected 32-bit register. -/
def mx (n : ℕ) : ℕ := if n % 2 = 1 then n / 2 ^^^ 0xEDB88320 else n / 2

/-- `mmAux 32 a b` is zlib's `multmodp(a, b)`: the product of the polynomials of `a` and `b`
mod `P`, reflected. -/
def mmAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, a, b => (if a.testBit n then b else 0) ^^^ mmAux n a (mx b)

theorem regPoly_eq_natPoly {D : ℕ} (r : BitVec D) : regPoly r = natPoly r.toNat D := by
  unfold regPoly natPoly
  exact Fin.sum_univ_eq_sum_range (fun i => if r.toNat.testBit i then X ^ (D - 1 - i) else 0) D

theorem natPoly_xor (a b D : ℕ) : natPoly (a ^^^ b) D = natPoly a D + natPoly b D := by
  unfold natPoly
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> simp [CharTwo.add_self_eq_zero]

theorem natPoly_zero (D : ℕ) : natPoly 0 D = 0 := by simp [natPoly]

theorem natPoly_degree (n D : ℕ) : (natPoly n D).degree < D := by
  rw [← Polynomial.mem_degreeLT]
  unfold natPoly
  refine Submodule.sum_mem _ fun i hi => ?_
  split_ifs
  · rw [Polynomial.mem_degreeLT, degree_X_pow]
    simp only [Finset.mem_range] at hi
    exact_mod_cast (by omega : D - 1 - i < D)
  · exact zero_mem _

theorem P_natDegree : crc32P.natDegree = 32 := by unfold crc32P; compute_degree!

theorem P_degree : crc32P.degree = 32 := by unfold crc32P; compute_degree!

theorem P_ne : crc32P ≠ 0 := by
  intro h; have := P_degree; rw [h] at this; simp at this

theorem mod_self_of_lt {p : (ZMod 2)[X]} (h : p.degree < 32) : p % crc32P = p :=
  (mod_eq_self_iff P_ne).2 (by rw [P_degree]; exact h)

theorem natPoly_mod (n : ℕ) : natPoly n 32 % crc32P = natPoly n 32 :=
  mod_self_of_lt (by have := natPoly_degree n 32; exact_mod_cast this)

theorem mod_mod' (a : (ZMod 2)[X]) : a % crc32P % crc32P = a % crc32P :=
  mod_self_of_lt (by have := degree_mod_lt a P_ne; rwa [P_degree] at this)

theorem mod_mul_mod (a b : (ZMod 2)[X]) : a % crc32P * b % crc32P = a * b % crc32P := by
  rw [mul_mod, mod_mod', ← mul_mod]

theorem mul_mod_mod (a b : (ZMod 2)[X]) : a * (b % crc32P) % crc32P = a * b % crc32P := by
  rw [mul_comm, mod_mul_mod, mul_comm]

theorem P_eq : crc32P = natPoly 0xEDB88320 32 + X ^ 32 := by
  simp [natPoly, crc32P, Finset.sum_range_succ, Nat.testBit]
  ring

theorem natPoly_shift (D n : ℕ) (hn : n < 2 ^ (D + 1)) :
    natPoly n (D + 1) * X = natPoly (n / 2) (D + 1) + if n.testBit 0 then X ^ (D + 1) else 0 := by
  unfold natPoly
  rw [Finset.sum_range_succ' (fun i => if n.testBit i then X ^ (D + 1 - 1 - i) else
      (0 : (ZMod 2)[X])) D,
    Finset.sum_range_succ (fun i => if (n / 2).testBit i then X ^ (D + 1 - 1 - i) else
      (0 : (ZMod 2)[X])) D]
  have h32 : (n / 2).testBit D = false := by
    rw [Nat.testBit_div_two]; exact Nat.testBit_eq_false_of_lt hn
  rw [h32, add_mul, Finset.sum_mul]
  simp only [Bool.false_eq_true, if_false, add_zero]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [Nat.testBit_div_two]
    split_ifs
    · rw [← pow_succ]; congr 1; omega
    · simp
  · split_ifs <;> simp [pow_succ]

theorem mx_spec (n : ℕ) (hn : n < 2 ^ 32) :
    mx n < 2 ^ 32 ∧ natPoly (mx n) 32 = natPoly n 32 * X % crc32P := by
  have hs := natPoly_shift 31 n hn
  have hlt : n / 2 < 2 ^ 32 := by omega
  unfold mx
  split_ifs with h
  · refine ⟨Nat.xor_lt_two_pow hlt (by norm_num), ?_⟩
    have h0 : n.testBit 0 = true := by simp [Nat.testBit_zero, h]
    rw [h0, if_pos rfl] at hs
    rw [hs, natPoly_xor]
    have e : natPoly (n / 2) (31 + 1) + X ^ (31 + 1) =
        natPoly (n / 2) 32 + natPoly 0xEDB88320 32 + crc32P := by
      rw [P_eq]
      have := CharTwo.add_self_eq_zero (natPoly 0xEDB88320 32)
      linear_combination -this
    rw [e, add_mod, EuclideanDomain.mod_self, add_zero, ← natPoly_xor, natPoly_mod]
  · refine ⟨hlt, ?_⟩
    have h0 : n.testBit 0 = false := by simp [Nat.testBit_zero, h]
    rw [h0] at hs
    simp only [Bool.false_eq_true, if_false, add_zero] at hs
    rw [hs, natPoly_mod]

theorem mx_iter (m : ℕ) : ∀ n, n < 2 ^ 32 →
    mx^[m] n < 2 ^ 32 ∧ natPoly (mx^[m] n) 32 = natPoly n 32 * X ^ m % crc32P := by
  induction m with
  | zero => intro n hn; exact ⟨by simpa using hn, by simp [natPoly_mod]⟩
  | succ m ih =>
    intro n hn
    obtain ⟨h1, h2⟩ := ih n hn
    obtain ⟨h3, h4⟩ := mx_spec _ h1
    rw [Function.iterate_succ_apply']
    refine ⟨h3, ?_⟩
    rw [h4, h2, mod_mul_mod, pow_succ, mul_assoc]

/-- The reflected-index polynomial that `mmAux n a` multiplies by. -/
noncomputable def Q (n a : ℕ) : (ZMod 2)[X] :=
  ∑ t ∈ Finset.range n, if a.testBit (n - 1 - t) then X ^ t else 0

theorem Q_succ (n a : ℕ) : Q (n + 1) a = X * Q n a + if a.testBit n then 1 else 0 := by
  unfold Q
  rw [Finset.sum_range_succ', Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun t _ => ?_
    have e : n + 1 - 1 - (t + 1) = n - 1 - t := by omega
    rw [e]; split_ifs <;> simp [pow_succ, mul_comm]

theorem mmAux_spec (n : ℕ) : ∀ a b, b < 2 ^ 32 →
    mmAux n a b < 2 ^ 32 ∧ natPoly (mmAux n a b) 32 = natPoly b 32 * Q n a % crc32P := by
  induction n with
  | zero => intro a b _; simp [mmAux, natPoly_zero, Q]
  | succ n ih =>
    intro a b hb
    obtain ⟨h1, h2⟩ := mx_spec b hb
    obtain ⟨h3, h4⟩ := ih a (mx b) h1
    have hite : (if a.testBit n then b else 0) < 2 ^ 32 := by split_ifs <;> omega
    refine ⟨Nat.xor_lt_two_pow hite h3, ?_⟩
    have key : natPoly (if a.testBit n then b else 0) 32 =
        natPoly b 32 * (if a.testBit n then 1 else 0) % crc32P := by
      split_ifs <;> simp [natPoly_mod, natPoly_zero]
    simp only [mmAux]
    rw [natPoly_xor, h4, h2, mod_mul_mod, Q_succ, key, mul_add,
      add_mod (natPoly b 32 * (X * Q n a)), mul_assoc]
    exact add_comm _ _

theorem Q_32 (a : ℕ) : Q 32 a = natPoly a 32 := by
  unfold Q natPoly
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [Finset.mem_range] at ht
  have e : 32 - 1 - (32 - 1 - t) = t := by omega
  rw [e]

theorem mm_spec (a b : ℕ) (hb : b < 2 ^ 32) :
    mmAux 32 a b < 2 ^ 32 ∧
      natPoly (mmAux 32 a b) 32 = natPoly b 32 * natPoly a 32 % crc32P := by
  rw [← Q_32 a]; exact mmAux_spec 32 a b hb

theorem natPoly_two_pow (k : ℕ) (hk : k < 32) : natPoly (2 ^ k) 32 = X ^ (31 - k) := by
  unfold natPoly
  simp only [Nat.testBit_two_pow]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; simp [Finset.mem_range] at h; omega

theorem natPoly_byte (i : ℕ) (hi : i < 256) : natPoly i 32 = natPoly i 8 * X ^ 24 := by
  unfold natPoly
  rw [show (32 : ℕ) = 8 + 24 from rfl, Finset.sum_range_add, Finset.sum_mul]
  have hz : ∑ x ∈ Finset.range 24,
      (if i.testBit (8 + x) then X ^ (8 + 24 - 1 - (8 + x)) else (0 : (ZMod 2)[X])) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Nat.testBit_eq_false_of_lt (by
      calc i < 2 ^ 8 := hi
        _ ≤ 2 ^ (8 + x) := Nat.pow_le_pow_right (by norm_num) (by omega))]
    simp
  rw [hz, add_zero]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  split_ifs
  · rw [← pow_add]; congr 1; omega
  · simp

theorem message_poly (M : Message) :
    M.poly = ∑ k ∈ Finset.range M.length, C (M.getD k 0) * X ^ (M.length - 1 - k) := by
  unfold Message.poly
  rw [← Fin.sum_univ_eq_sum_range (fun k => C (M.getD k 0) * X ^ (M.length - 1 - k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [List.getD_eq_getElem?_getD]

theorem byte_poly (i : ℕ) :
    (Message.ofBytes [BitVec.ofNat 8 i]).poly = natPoly i 8 := by
  rw [message_poly]
  have hl : (Message.ofBytes [BitVec.ofNat 8 i]).length = 8 := by simp [Message.ofBytes]
  rw [hl]
  unfold natPoly
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  have hg : (Message.ofBytes [BitVec.ofNat 8 i]).getD k 0 =
      if i.testBit k then 1 else 0 := by
    simp only [Message.ofBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    have hb : ∀ k (h : k < 8), (BitVec.ofNat 8 i)[k] = i.testBit k := fun k h => by
      rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow]
      simp [h]
    interval_cases k <;> simp [hb]
  rw [hg]
  split_ifs <;> simp

end ZlibCrc32Tables

namespace ZlibCrc32Tables

/-- Walk a byte list four bytes at a time, checking each little-endian word against `f`. -/
def chk (f : ℕ → ℕ) : ℕ → List (BitVec 8) → Bool
  | i, b0 :: b1 :: b2 :: b3 :: rest =>
    (b3 ++ b2 ++ b1 ++ b0 == BitVec.ofNat 32 (f i)) && chk f (i + 1) rest
  | _, [] => true
  | _, _ => false

/-- As `chk`, for the squaring sequence `c, c², c⁴, …` (mod `P`). -/
def chkX : ℕ → List (BitVec 8) → Bool
  | c, b0 :: b1 :: b2 :: b3 :: rest =>
    (b3 ++ b2 ++ b1 ++ b0 == BitVec.ofNat 32 c) && chkX (mmAux 32 c c) rest
  | _, [] => true
  | _, _ => false

theorem word32_zero (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8)) :
    word32 (b0 :: b1 :: b2 :: b3 :: rest) 0 = b3 ++ b2 ++ b1 ++ b0 := by
  simp [word32]

theorem word32_succ (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8)) (i : ℕ) :
    word32 (b0 :: b1 :: b2 :: b3 :: rest) (i + 1) = word32 rest i := by
  unfold word32
  have e0 : 4 * (i + 1) = 4 * i + 1 + 1 + 1 + 1 := by ring
  simp only [e0, List.getD_cons_succ]

theorem chk_spec (f : ℕ → ℕ) (i : ℕ) : ∀ (j : ℕ) (L : List (BitVec 8)),
    chk f j L = true → i < L.length / 4 → word32 L i = BitVec.ofNat 32 (f (j + i)) := by
  induction i with
  | zero =>
    intro j L h hi
    match L, h, hi with
    | b0 :: b1 :: b2 :: b3 :: rest, h, _ =>
      simp only [chk, Bool.and_eq_true, beq_iff_eq] at h
      rw [word32_zero, h.1, Nat.add_zero]
    | [], _, hi => simp at hi
    | [_], _, hi => simp at hi
    | [_, _], _, hi => simp at hi
    | [_, _, _], _, hi => simp at hi
  | succ i ih =>
    intro j L h hi
    match L, h, hi with
    | b0 :: b1 :: b2 :: b3 :: rest, h, hi =>
      simp only [chk, Bool.and_eq_true] at h
      rw [word32_succ, ih (j + 1) rest h.2 (by simp at hi; omega)]
      congr 2; omega
    | [], _, hi => simp at hi
    | [_], _, hi => simp at hi
    | [_, _], _, hi => simp at hi
    | [_, _, _], _, hi => simp at hi

theorem chkX_spec (i : ℕ) : ∀ (c : ℕ) (L : List (BitVec 8)),
    chkX c L = true → i < L.length / 4 →
      word32 L i = BitVec.ofNat 32 ((fun a => mmAux 32 a a)^[i] c) := by
  induction i with
  | zero =>
    intro c L h hi
    match L, h, hi with
    | b0 :: b1 :: b2 :: b3 :: rest, h, _ =>
      simp only [chkX, Bool.and_eq_true, beq_iff_eq] at h
      rw [word32_zero, h.1]; rfl
    | [], _, hi => simp at hi
    | [_], _, hi => simp at hi
    | [_, _], _, hi => simp at hi
    | [_, _, _], _, hi => simp at hi
  | succ i ih =>
    intro c L h hi
    match L, h, hi with
    | b0 :: b1 :: b2 :: b3 :: rest, h, hi =>
      simp only [chkX, Bool.and_eq_true] at h
      rw [word32_succ, ih _ rest h.2 (by simp at hi; omega), Function.iterate_succ_apply]
    | [], _, hi => simp at hi
    | [_], _, hi => simp at hi
    | [_, _], _, hi => simp at hi
    | [_, _, _], _, hi => simp at hi

/-- The braid constants `x^(320 - 8k) mod P`, reflected, `k < 8`. -/
def ctab : List ℕ :=
  [0xa700e96a, 0x67cf0be4, 0x1241289b, 0xf6c1cb59, 0x78ed02d5, 0xeacb7748, 0x1e307184,
    0x3183ec92]

theorem len0 : zlibCrc32PlacedData0.length = 1024 := by decide +kernel
theorem len1 : zlibCrc32PlacedData1.length = 8192 := by decide +kernel
theorem len2 : zlibCrc32PlacedData2.length = 128 := by decide +kernel

theorem chk0 : chk (fun i => mx^[8] i) 0 zlibCrc32PlacedData0 = true := by decide +kernel

theorem chk1 :
    chk (fun j => mmAux 32 (ctab.getD (j / 256) 0) (j % 256)) 0 zlibCrc32PlacedData1 = true := by
  decide +kernel

theorem chk2 : chkX (2 ^ 30) zlibCrc32PlacedData2 = true := by decide +kernel

theorem ctab_eq : ∀ k < 8, ctab.getD k 0 = mx^[320 - 8 * k] (2 ^ 31) := by decide +kernel

theorem regPoly_ofNat (v : ℕ) (hv : v < 2 ^ 32) : regPoly (BitVec.ofNat 32 v) = natPoly v 32 := by
  rw [regPoly_eq_natPoly, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

theorem table0 (i : ℕ) (hi : i < 256) :
    regPoly (word32 zlibCrc32PlacedData0 i) =
      crc0 crc32P (Message.ofBytes [BitVec.ofNat 8 i]) 0 := by
  rw [chk_spec _ i 0 _ chk0 (by rw [len0]; omega), Nat.zero_add]
  obtain ⟨h1, h2⟩ := mx_iter 8 i (by omega)
  rw [regPoly_ofNat _ h1, h2, natPoly_byte i hi, crc0, byte_poly, P_natDegree, zero_mul,
    zero_add, mul_assoc, ← pow_add]

theorem table1 (k : ℕ) (hk : k < 8) (i : ℕ) (hi : i < 256) :
    regPoly (word32 zlibCrc32PlacedData1 (256 * k + i)) =
      (Message.ofBytes [BitVec.ofNat 8 i]).poly * X ^ (8 * (5 * 8 + 3 - k)) % crc32P := by
  rw [chk_spec _ _ 0 _ chk1 (by rw [len1]; omega), Nat.zero_add]
  have e1 : (256 * k + i) / 256 = k := by omega
  have e2 : (256 * k + i) % 256 = i := by omega
  rw [e1, e2, ctab_eq k hk]
  obtain ⟨hc1, hc2⟩ := mx_iter (320 - 8 * k) (2 ^ 31) (by norm_num)
  obtain ⟨hm1, hm2⟩ := mm_spec (mx^[320 - 8 * k] (2 ^ 31)) i (by omega)
  rw [regPoly_ofNat _ hm1, hm2, hc2, natPoly_two_pow 31 (by norm_num), mul_mod_mod,
    natPoly_byte i hi, byte_poly, Nat.sub_self, pow_zero, one_mul, mul_assoc, ← pow_add]
  congr 3; omega

theorem table2 (k : ℕ) (hk : k < 32) :
    regPoly (word32 zlibCrc32PlacedData2 k) = pow2k crc32P k := by
  rw [chkX_spec k _ _ chk2 (by rw [len2]; omega), pow2k]
  have key : ∀ m, (fun a => mmAux 32 a a)^[m] (2 ^ 30) < 2 ^ 32 ∧
      natPoly ((fun a => mmAux 32 a a)^[m] (2 ^ 30)) 32 = X ^ (2 ^ m) % crc32P := by
    intro m
    induction m with
    | zero =>
      refine ⟨by norm_num, ?_⟩
      rw [Function.iterate_zero_apply, natPoly_two_pow 30 (by norm_num), pow_zero, pow_one,
        mod_self_of_lt (by rw [degree_X]; norm_num)]
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨h1, h2⟩ := mm_spec _ _ ih.1
      refine ⟨h1, ?_⟩
      rw [h2, ih.2, mul_mod_mod, mod_mul_mod, ← pow_add, pow_succ, mul_two]
  rw [regPoly_ofNat _ (key k).1, (key k).2]

theorem crc_tables_eq_dev :
    (zlibCrc32PlacedData0.length = 1024 ∧ ∀ i < 256,
      regPoly (word32 zlibCrc32PlacedData0 i) = crc0 crc32P (Message.ofBytes [BitVec.ofNat 8 i]) 0) ∧
    (zlibCrc32PlacedData1.length = 8192 ∧ ∀ k < 8, ∀ i < 256,
      regPoly (word32 zlibCrc32PlacedData1 (256 * k + i)) =
        (Message.ofBytes [BitVec.ofNat 8 i]).poly * X ^ (8 * (5 * 8 + 3 - k)) % crc32P) ∧
    (zlibCrc32PlacedData2.length = 128 ∧ ∀ k < 32,
      regPoly (word32 zlibCrc32PlacedData2 k) = pow2k crc32P k) :=
  ⟨⟨len0, table0⟩, ⟨len1, table1⟩, ⟨len2, table2⟩⟩

end ZlibCrc32Tables

theorem solution :
    (zlibCrc32PlacedData0.length = 1024 ∧ ∀ i < 256,
      regPoly (word32 zlibCrc32PlacedData0 i) = crc0 crc32P (Message.ofBytes [BitVec.ofNat 8 i]) 0) ∧
    (zlibCrc32PlacedData1.length = 8192 ∧ ∀ k < 8, ∀ i < 256,
      regPoly (word32 zlibCrc32PlacedData1 (256 * k + i)) =
        (Message.ofBytes [BitVec.ofNat 8 i]).poly * X ^ (8 * (5 * 8 + 3 - k)) % crc32P) ∧
    (zlibCrc32PlacedData2.length = 128 ∧ ∀ k < 32,
      regPoly (word32 zlibCrc32PlacedData2 k) = pow2k crc32P k) :=
  ZlibCrc32Tables.crc_tables_eq_dev
