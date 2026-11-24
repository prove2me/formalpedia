-- Prove2me | solution 1 for Poly1305Boringssl.poly1305Mac_eq_poly1305
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-24T10:20:33.583513+00:00
-- url     : https://prove2.me/submissions/cc177b35-c5e2-4c52-a079-90bf13598deb

import Definitions.Def_Poly1305Boringssl_Rfc8439
import Definitions.Def_Poly1305Bernstein
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases

/-!
# RFC 8439 `poly1305_mac` equals Bernstein's `Poly1305_r(m, s)`

`Poly1305Boringssl.chk_poly1305Mac_eq_poly1305`: the RFC transcription `poly1305Mac` and
Bernstein's `Poly1305.poly1305` agree, with `r` the clamped first key half (bytewise AND with the
clamp mask) and `s` the second key half.
-/

namespace Poly1305Boringssl.BridgeMac

open Finset

/-! ## Little-endian values as positional sums -/

theorem getD_of_lt {α : Type} (l : List α) (i : ℕ) (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem leBytesToNum_sum (l : List (BitVec 8)) :
    leBytesToNum l = ∑ j ∈ range l.length, 256 ^ j * (l.getD j 0).toNat := by
  induction l with
  | nil => simp [leBytesToNum]
  | cons b bs ih =>
    have h : leBytesToNum (b :: bs) = b.toNat + 256 * leBytesToNum bs := rfl
    rw [h, ih, List.length_cons, sum_range_succ', mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, one_mul, pow_succ]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    ring

theorem leBytesToNum_append_one (l : List (BitVec 8)) :
    leBytesToNum (l ++ [1#8]) = leBytesToNum l + 256 ^ l.length := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    have h1 : leBytesToNum (b :: bs ++ [1#8]) = b.toNat + 256 * leBytesToNum (bs ++ [1#8]) := rfl
    have h2 : leBytesToNum (b :: bs) = b.toNat + 256 * leBytesToNum bs := rfl
    rw [h1, h2, ih, List.length_cons, pow_succ]
    ring

theorem leBytesToNum_digit : ∀ (l : List (BitVec 8)) (j : ℕ),
    leBytesToNum l / 256 ^ j % 256 = (l.getD j 0).toNat
  | [], j => by simp [leBytesToNum]
  | b :: bs, 0 => by
    have h : leBytesToNum (b :: bs) = b.toNat + 256 * leBytesToNum bs := rfl
    rw [h]; simp only [pow_zero, Nat.div_one, List.getD_cons_zero]
    have := b.isLt
    omega
  | b :: bs, j + 1 => by
    have h : leBytesToNum (b :: bs) = b.toNat + 256 * leBytesToNum bs := rfl
    rw [h, List.getD_cons_succ, ← leBytesToNum_digit bs j, pow_succ', ← Nat.div_div_eq_div_mul]
    congr 2
    have := b.isLt
    omega

theorem leBytesToNum_lt (l : List (BitVec 8)) : leBytesToNum l < 256 ^ l.length := by
  induction l with
  | nil => simp [leBytesToNum]
  | cons b bs ih =>
    have h : leBytesToNum (b :: bs) = b.toNat + 256 * leBytesToNum bs := rfl
    rw [h, List.length_cons, pow_succ']
    have := b.isLt
    omega

/-! ## Bytewise AND -/

theorem and_byte (x y : ℕ) :
    x &&& y = (x % 256 &&& y % 256) + 256 * (x / 256 &&& y / 256) := by
  have h1 := Nat.and_mod_two_pow (a := x) (b := y) (n := 8)
  have h2 := Nat.and_div_two_pow (a := x) (b := y) (n := 8)
  norm_num at h1 h2
  rw [← h1, ← h2]
  exact (Nat.mod_add_div _ _).symm

theorem and_bytes (x y : ℕ) : ∀ n : ℕ,
    x &&& y = (∑ j ∈ range n, 256 ^ j * (x / 256 ^ j % 256 &&& y / 256 ^ j % 256)) +
      256 ^ n * (x / 256 ^ n &&& y / 256 ^ n)
  | 0 => by simp
  | n + 1 => by
    rw [and_bytes x y n, sum_range_succ, and_byte (x / 256 ^ n) (y / 256 ^ n),
      Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_succ]
    ring

/-- The clamp mask, byte by byte. -/
def maskAt (k : ℕ) : ℕ :=
  [0xff, 0xff, 0xff, 0x0f, 0xfc, 0xff, 0xff, 0x0f, 0xfc, 0xff, 0xff, 0x0f, 0xfc, 0xff, 0xff,
    0x0f].getD k 0

theorem mask_digit (j : ℕ) (hj : j < 16) :
    (0x0ffffffc0ffffffc0ffffffc0fffffff : ℕ) / 256 ^ j % 256 = maskAt j := by
  interval_cases j <;> decide

theorem clamp_eq (l : List (BitVec 8)) (hl : l.length = 16) :
    clamp (leBytesToNum l) = ∑ j ∈ range 16, 256 ^ j * ((l.getD j 0).toNat &&& maskAt j) := by
  unfold clamp
  rw [and_bytes _ _ 16]
  have hlt := leBytesToNum_lt l
  rw [hl] at hlt
  rw [Nat.div_eq_of_lt hlt, Nat.zero_and, mul_zero, add_zero]
  refine sum_congr rfl fun j hj => ?_
  rw [leBytesToNum_digit, mask_digit j (mem_range.mp hj)]

/-! ## The RFC loop -/

theorem foldl_eq (R : ℕ) (c : ℕ → ℕ) : ∀ n : ℕ,
    (List.range n).foldl (fun a i => R * (a + c i) % p1305) 0 =
      (∑ i ∈ range n, c i * R ^ (n - i)) % p1305
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_eq R c n, List.foldl_cons, List.foldl_nil,
      sum_range_succ, show n + 1 - n = 1 by omega, pow_one]
    have : ∑ i ∈ range n, c i * R ^ (n + 1 - i) = R * ∑ i ∈ range n, c i * R ^ (n - i) := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      have : n + 1 - i = (n - i) + 1 := by have := mem_range.mp hi; omega
      rw [this, pow_succ]; ring
    rw [this, Nat.mul_mod, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, ← Nat.mul_mod]
    congr 1; ring

theorem sum_Icc_one (F : ℕ → ℕ) : ∀ n : ℕ, ∑ i ∈ Icc 1 n, F i = ∑ i ∈ range n, F (i + 1)
  | 0 => by simp
  | n + 1 => by
    rw [sum_Icc_succ_top (by omega), sum_Icc_one F n, sum_range_succ]

/-! ## Blocks are Bernstein's chunks -/

/-- The byte embedding of the statement. -/
def toByte (b : BitVec 8) : Poly1305.Byte := ⟨b.toNat, b.isLt⟩

theorem byteAt_map (msg : List (BitVec 8)) (k : ℕ) (hk : k < msg.length) :
    Poly1305.byteAt (msg.map toByte) k = (msg.getD k 0).toNat := by
  unfold Poly1305.byteAt
  rw [getD_of_lt _ _ _ (by simpa using hk), getD_of_lt _ _ _ hk]
  simp [toByte]

theorem block_eq_chunk (msg : List (BitVec 8)) (i : ℕ) (hi : i < (msg.length + 15) / 16) :
    leBytesToNum ((msg.drop (16 * i)).take 16 ++ [1#8]) = Poly1305.chunk (msg.map toByte) (i + 1) := by
  set L := min 16 (msg.length - 16 * i) with hL
  have hlen : ((msg.drop (16 * i)).take 16).length = L := by simp [hL]
  have hsum : leBytesToNum ((msg.drop (16 * i)).take 16) =
      ∑ j ∈ range L, 2 ^ (8 * j) * Poly1305.byteAt (msg.map toByte) (16 * (i + 1) - 16 + j) := by
    rw [leBytesToNum_sum, hlen]
    refine sum_congr rfl fun j hj => ?_
    have hj := mem_range.mp hj
    rw [pow_mul, show (2 : ℕ) ^ 8 = 256 by norm_num, show 16 * (i + 1) - 16 + j = 16 * i + j by omega,
      byteAt_map _ _ (by omega)]
    congr 2
    rw [getD_of_lt _ _ _ (by omega), getD_of_lt _ _ _ (by omega)]
    simp
  rw [leBytesToNum_append_one, hsum, hlen]
  unfold Poly1305.chunk
  simp only [List.length_map]
  split_ifs with h
  · have : L = 16 := by omega
    rw [this]; norm_num
  · have : L = msg.length % 16 := by omega
    rw [this, pow_mul]; norm_num

theorem accumulate_eq (R : ℕ) (msg : List (BitVec 8)) :
    accumulate R 0 msg =
      (∑ i ∈ Icc 1 (Poly1305.numChunks (msg.map toByte)),
        Poly1305.chunk (msg.map toByte) i * R ^ (Poly1305.numChunks (msg.map toByte) + 1 - i)) %
        Poly1305.p1305 := by
  have hq : Poly1305.numChunks (msg.map toByte) = (msg.length + 15) / 16 := by
    simp [Poly1305.numChunks]
  rw [hq, sum_Icc_one, show Poly1305.p1305 = p1305 from rfl]
  unfold accumulate
  rw [foldl_eq]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  rw [block_eq_chunk msg i (mem_range.mp hi)]
  congr 2
  omega

/-! ## Output bytes -/

theorem out_byte (Z j : ℕ) (hj : j < 16) : Z % 2 ^ 128 / 2 ^ (8 * j) % 256 = Z / 256 ^ j % 256 := by
  have h : (2 : ℕ) ^ 128 = 2 ^ (8 * j) * 2 ^ (128 - 8 * j) := by rw [← pow_add]; congr 1; omega
  rw [h, Nat.mod_mul_right_div_self, pow_mul, show (2 : ℕ) ^ 8 = 256 by norm_num]
  refine Nat.mod_mod_of_dvd _ ?_
  have : 128 - 8 * j = 8 + (120 - 8 * j) := by omega
  rw [this, pow_add]; exact Dvd.intro _ rfl

/-! ## The key halves -/

/-- The clamped first key half, byte by byte. -/
def rStr (key : List (BitVec 8)) : Poly1305.Str16 := fun j =>
  ⟨(key.getD j 0).toNat &&& maskAt j, lt_of_le_of_lt Nat.and_le_left (key.getD j 0).isLt⟩

/-- The second key half. -/
def sStr (key : List (BitVec 8)) : Poly1305.Str16 := fun j =>
  ⟨(key.getD (16 + j) 0).toNat, (key.getD (16 + j) 0).isLt⟩

theorem and_mod4 (x m : ℕ) (hm : m % 4 = 0) : (x &&& m) % 4 = 0 := by
  rw [show (4 : ℕ) = 2 ^ 2 from rfl, Nat.and_mod_two_pow, show (2 : ℕ) ^ 2 = 4 from rfl, hm,
    Nat.and_zero]

theorem rStr_clamped (key : List (BitVec 8)) : Poly1305.IsClamped (rStr key) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.and_lt_two_pow _ (n := 4) (by decide)
  · exact Nat.and_lt_two_pow _ (n := 4) (by decide)
  · exact Nat.and_lt_two_pow _ (n := 4) (by decide)
  · exact Nat.and_lt_two_pow _ (n := 4) (by decide)
  · exact and_mod4 _ _ (by decide)
  · exact and_mod4 _ _ (by decide)
  · exact and_mod4 _ _ (by decide)

theorem leVal_rStr (key : List (BitVec 8)) (hkey : key.length = 32) :
    Poly1305.leVal (rStr key) = clamp (leBytesToNum (key.take 16)) := by
  rw [clamp_eq _ (by simp [hkey]), Poly1305.leVal, ← Fin.sum_univ_eq_sum_range]
  refine Fintype.sum_congr _ _ fun j => ?_
  have hj := j.isLt
  rw [pow_mul, show (2 : ℕ) ^ 8 = 256 by norm_num]
  show _ * ((key.getD j 0).toNat &&& maskAt j) = _
  rw [getD_of_lt _ _ _ (by omega), getD_of_lt _ _ _ (by rw [List.length_take, hkey]; omega)]
  simp

theorem leVal_sStr (key : List (BitVec 8)) (hkey : key.length = 32) :
    Poly1305.leVal (sStr key) = leBytesToNum (key.drop 16) := by
  have hl : (key.drop 16).length = 16 := by simp [hkey]
  rw [leBytesToNum_sum, hl, Poly1305.leVal, ← Fin.sum_univ_eq_sum_range]
  refine Fintype.sum_congr _ _ fun j => ?_
  have hj := j.isLt
  rw [pow_mul, show (2 : ℕ) ^ 8 = 256 by norm_num]
  show _ * (key.getD (16 + j) 0).toNat = _
  rw [getD_of_lt _ _ _ (by omega), getD_of_lt _ _ _ (by omega)]
  simp

end Poly1305Boringssl.BridgeMac

namespace Poly1305Boringssl

open Finset BridgeMac

theorem chk_poly1305Mac_eq_poly1305 (key msg : List (BitVec 8)) (hkey : key.length = 32) :
    ∃ r s : Poly1305.Str16, Poly1305.IsClamped r ∧
      Poly1305.leVal r = clamp (leBytesToNum (key.take 16)) ∧
      Poly1305.leVal s = leBytesToNum (key.drop 16) ∧
      (poly1305Mac msg key).map BitVec.toNat =
        List.ofFn fun j =>
          ((Poly1305.poly1305 (Poly1305.leVal r) (msg.map fun b => (⟨b.toNat, b.isLt⟩ : Poly1305.Byte)) s j :
            Poly1305.Byte) : Nat) := by
  have hr := leVal_rStr key hkey
  have hs := leVal_sStr key hkey
  refine ⟨rStr key, sStr key, rStr_clamped key, hr, hs, ?_⟩
  have hS : leBytesToNum ((key.drop 16).take 16) = Poly1305.leVal (sStr key) := by
    rw [List.take_of_length_le (by simp [hkey]), hs]
  have hA : accumulate (clamp (leBytesToNum (key.take 16))) 0 msg =
      (∑ i ∈ Icc 1 (Poly1305.numChunks (msg.map toByte)),
        Poly1305.chunk (msg.map toByte) i *
          Poly1305.leVal (rStr key) ^ (Poly1305.numChunks (msg.map toByte) + 1 - i)) %
        Poly1305.p1305 := by
    rw [← hr, accumulate_eq]
  unfold poly1305Mac
  rw [hS, hA]
  apply List.ext_getElem
  · simp [numTo16LeBytes]
  · intro j h1 h2
    simp only [numTo16LeBytes, List.length_map, List.length_range] at h1
    simp only [numTo16LeBytes, List.getElem_map, List.getElem_range, List.getElem_ofFn,
      BitVec.toNat_ofNat, Poly1305.poly1305, Poly1305.toStr16]
    rw [out_byte _ _ h1]
    rfl


end Poly1305Boringssl

open Poly1305Boringssl in
theorem solution (key msg : List (BitVec 8)) (hkey : key.length = 32) :
    ∃ r s : Poly1305.Str16, Poly1305.IsClamped r ∧
      Poly1305.leVal r = clamp (leBytesToNum (key.take 16)) ∧
      Poly1305.leVal s = leBytesToNum (key.drop 16) ∧
      (poly1305Mac msg key).map BitVec.toNat =
        List.ofFn fun j =>
          ((Poly1305.poly1305 (Poly1305.leVal r) (msg.map fun b => (⟨b.toNat, b.isLt⟩ : Poly1305.Byte)) s j :
            Poly1305.Byte) : Nat) :=
  Poly1305Boringssl.chk_poly1305Mac_eq_poly1305 key msg hkey
