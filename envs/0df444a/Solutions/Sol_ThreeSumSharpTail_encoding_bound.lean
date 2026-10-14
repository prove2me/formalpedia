-- Prove2me | solution 1 for ThreeSumSharpTail.encoding_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T17:14:08.563164+00:00
-- url     : https://prove2.me/submissions/b1cabd15-9bd9-4a10-954d-8e3557d72598

import Definitions.Def_ThreeSumSharpTail_Analysis
import Theorems.Thm_ThreeSumSharpTail_binomial_entropy_bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

open ThreeSumSharpTail

theorem solution (c m : ℕ) (hc : 10 < c) (hm : 1 ≤ m) :
    (10 : ℝ) ^ (c * m) / Real.sqrt (boxCount c m 0 : ℝ) ≤
      Real.sqrt (c * m + 1 : ℝ) * (4 ^ m : ℝ) ^ encodingExponent c := by
  have hc0 : 0 < c := by omega
  have hm0 : 0 < m := by omega
  have hcm : m ≤ c * m := by nlinarith
  have hcm1 : 1 ≤ c * m := by omega
  have hbox : boxCount c m 0 = Nat.choose (c * m) m * 9 ^ ((c - 1) * m) := by
    simp only [boxCount, Nat.sub_zero]
    congr 1
    rw [Nat.sub_mul]
    simp
  have hbin := (binomial_entropy_bounds (c * m) m hcm1 hcm).1
  have hfrac : (m : ℝ) / (c * m : ℕ) = 1 / c := by
    have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hc0)
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm0)
    push_cast
    field_simp
  rw [hfrac] at hbin
  have hpow3 : (9 : ℝ) ^ ((c - 1) * m) = Real.exp ((((c - 1) * m : ℕ) : ℝ) * Real.log 9) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 9)]
    rw [mul_comm]
  have hboxlower :
      Real.exp ((c * m : ℝ) * entropy (1 / c)) / ((c * m : ℝ) + 1) *
          Real.exp ((((c - 1) * m : ℕ) : ℝ) * Real.log 9) ≤ (boxCount c m 0 : ℝ) := by
    have hbin' :
        Real.exp ((c * m : ℝ) * entropy (1 / c)) / ((c * m : ℝ) + 1) ≤
          (Nat.choose (c * m) m : ℝ) := by
      simpa only [Nat.cast_mul] using hbin
    calc
      _ ≤ (Nat.choose (c * m) m : ℝ) *
          Real.exp ((((c - 1) * m : ℕ) : ℝ) * Real.log 9) :=
        mul_le_mul_of_nonneg_right hbin' (Real.exp_nonneg _)
      _ = (boxCount c m 0 : ℝ) := by
        rw [hbox]
        push_cast
        rw [hpow3]
        have hcastprod : (((c - 1) * m : ℕ) : ℝ) =
            ((c - 1 : ℕ) : ℝ) * (m : ℝ) := by norm_num
        rw [← hcastprod]
  have hboxpos : 0 < (boxCount c m 0 : ℝ) := by
    apply Nat.cast_pos.mpr
    rw [hbox]
    exact Nat.mul_pos (Nat.choose_pos hcm) (by positivity)
  have hrootlower :
      Real.sqrt (Real.exp ((c * m : ℝ) * entropy (1 / c)) / ((c * m : ℝ) + 1) *
          Real.exp ((((c - 1) * m : ℕ) : ℝ) * Real.log 9)) ≤
        Real.sqrt (boxCount c m 0 : ℝ) := Real.sqrt_le_sqrt hboxlower
  have hexpsqrt (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
    congr 1
    ring
  have hrootid :
      Real.sqrt (Real.exp ((c * m : ℝ) * entropy (1 / c)) / ((c * m : ℝ) + 1) *
          Real.exp ((((c - 1) * m : ℕ) : ℝ) * Real.log 9)) =
        Real.exp ((c * m : ℝ) * entropy (1 / c) / 2 +
          (((c - 1) * m : ℕ) : ℝ) * Real.log 9 / 2) /
          Real.sqrt ((c * m : ℝ) + 1) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_div (by positivity),
      hexpsqrt, hexpsqrt]
    calc
      Real.exp ((c * m : ℝ) * entropy (1 / c) / 2) /
          Real.sqrt ((c * m : ℝ) + 1) *
          Real.exp ((((c - 1) * m : ℕ) : ℝ) * Real.log 9 / 2) =
          (Real.exp ((c * m : ℝ) * entropy (1 / c) / 2) *
            Real.exp ((((c - 1) * m : ℕ) : ℝ) * Real.log 9 / 2)) /
              Real.sqrt ((c * m : ℝ) + 1) := by ring
      _ = _ := by rw [← Real.exp_add]
  have hencoding :
      Real.exp ((c * m : ℝ) * Real.log 10 -
          (c * m : ℝ) * entropy (1 / c) / 2 -
          (((c - 1) * m : ℕ) : ℝ) * Real.log 9 / 2) =
        (4 ^ m : ℝ) ^ encodingExponent c := by
    rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (4 ^ m : ℝ)), Real.log_pow]
    apply congrArg Real.exp
    have hlog9 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [hlog9]
    unfold encodingExponent entropy
    field_simp
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ c)]
    ring
  have hdenroot : Real.sqrt ((c * m : ℝ) + 1) > 0 := by positivity
  have hencpos : 0 < (4 ^ m : ℝ) ^ encodingExponent c := Real.rpow_pos_of_pos (by positivity) _
  have hrootpos := Real.sqrt_pos.2 hboxpos
  apply (div_le_iff₀ hrootpos).2
  have hmul := mul_le_mul_of_nonneg_right hrootlower (mul_nonneg hdenroot.le hencpos.le)
  rw [hrootid] at hmul
  have hpow10 : (10 : ℝ) ^ (c * m) = Real.exp ((c * m : ℝ) * Real.log 10) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 10)]
    congr 1
    rw [Nat.cast_mul]
    ring
  have hkey :
      Real.exp ((c * m : ℝ) * Real.log 10) =
        Real.exp ((c * m : ℝ) * entropy (1 / c) / 2 +
          (((c - 1) * m : ℕ) : ℝ) * Real.log 9 / 2) *
          (4 ^ m : ℝ) ^ encodingExponent c := by
    rw [← hencoding, ← Real.exp_add]
    congr 1
    ring
  have hmul' := hmul
  have hmain : (10 : ℝ) ^ (c * m) ≤
      Real.sqrt ((c * m : ℝ) + 1) * (4 ^ m : ℝ) ^ encodingExponent c *
        Real.sqrt (boxCount c m 0 : ℝ) := by
    calc
      (10 : ℝ) ^ (c * m) =
          Real.exp ((c * m : ℝ) * entropy (1 / c) / 2 +
            (((c - 1) * m : ℕ) : ℝ) * Real.log 9 / 2) *
            (4 ^ m : ℝ) ^ encodingExponent c := hpow10.trans hkey
      _ = (Real.exp ((c * m : ℝ) * entropy (1 / c) / 2 +
            (((c - 1) * m : ℕ) : ℝ) * Real.log 9 / 2) /
            Real.sqrt ((c * m : ℝ) + 1)) *
            (Real.sqrt ((c * m : ℝ) + 1) * (4 ^ m : ℝ) ^ encodingExponent c) := by
          field_simp [ne_of_gt hdenroot]
      _ ≤ Real.sqrt (boxCount c m 0 : ℝ) *
            (Real.sqrt ((c * m : ℝ) + 1) * (4 ^ m : ℝ) ^ encodingExponent c) := hmul'
      _ = Real.sqrt ((c * m : ℝ) + 1) *
            (4 ^ m : ℝ) ^ encodingExponent c * Real.sqrt (boxCount c m 0 : ℝ) := by ring
  exact hmain

#print axioms solution
