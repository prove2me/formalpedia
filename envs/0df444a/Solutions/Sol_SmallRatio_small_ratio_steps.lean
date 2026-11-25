-- Prove2me | solution 1 for SmallRatio.small_ratio_steps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:40:35.740315+00:00
-- url     : https://prove2.me/submissions/66503eee-adbf-4053-a152-d9fe63797e37

module
public import Definitions.Def_SmallRatio_AlongEuclid
public import Definitions.Def_SmallRatio_Legendre
public import Definitions.Def_SmallRatio_Main
public import Theorems.Thm_SmallRatio_coprime_p_h
public import Theorems.Thm_SmallRatio_smallRatioSum_eq
public import Theorems.Thm_SmallRatio_dedekind_along_euclid
public import Theorems.Thm_SmallRatio_den_pos
public import Theorems.Thm_SmallRatio_pos_rem_of_le_steps


set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p)
include hp hh hhp
namespace SmallRatio
theorem _root_.solution :
    |12 * dedekindSum h p - p * smallRatioSum p h| ≤ 6 * steps p h := by
  have hc := coprime_p_h hp hh hhp
  have h1 := dedekind_along_euclid hh hhp hc
  set n := steps p h
  set A := ∑ i ∈ Icc 1 n, (-1) ^ (i + 1) * ((p : ℚ) / ((rem p h i : ℚ) * den p h i))
  have h2 : |A - p * smallRatioSum p h| ≤ 2 * n := by
    rw [smallRatioSum_eq hp hh hhp, mul_sum, ← sum_sub_distrib]
    calc |∑ i ∈ Icc 1 n, ((-1) ^ (i + 1) * ((p : ℚ) / ((rem p h i : ℚ) * den p h i)) -
            p * (if 2 * rem p h i * den p h i < p then
              (-1) ^ (i + 1) / ((rem p h i : ℚ) * den p h i) else 0))|
        ≤ ∑ i ∈ Icc 1 n, |(-1) ^ (i + 1) * ((p : ℚ) / ((rem p h i : ℚ) * den p h i)) -
            p * (if 2 * rem p h i * den p h i < p then
              (-1) ^ (i + 1) / ((rem p h i : ℚ) * den p h i) else 0)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Icc 1 n, (2 : ℚ) := by
          apply sum_le_sum
          intro i hi
          rw [mem_Icc] at hi
          by_cases hs : 2 * rem p h i * den p h i < p
          · rw [if_pos hs, mul_div_assoc', mul_comm (p : ℚ), div_mul_eq_mul_div, sub_self, abs_zero]
            norm_num
          · rw [if_neg hs, mul_zero, sub_zero, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
            have hr := pos_rem_of_le_steps hh hhp hc hi.2
            have hd := den_pos hh hhp hc hi.1 (by omega)
            have hpos : (0 : ℚ) < (rem p h i : ℚ) * den p h i := by positivity
            rw [abs_of_nonneg (by positivity), div_le_iff₀ hpos]
            have : (p : ℚ) ≤ 2 * rem p h i * den p h i := by exact_mod_cast (not_lt.1 hs)
            linarith
      _ = 2 * n := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
  calc |12 * dedekindSum h p - p * smallRatioSum p h|
      = |(12 * dedekindSum h p - A) + (A - p * smallRatioSum p h)| := by ring_nf
    _ ≤ |12 * dedekindSum h p - A| + |A - p * smallRatioSum p h| := abs_add_le _ _
    _ ≤ 4 * n + 2 * n := add_le_add h1 h2
    _ = 6 * n := by ring
end SmallRatio
