-- Prove2me | solution 1 for ThreeSumSharpTail.pruned_encoding_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T17:39:09.278461+00:00
-- url     : https://prove2.me/submissions/0b950f89-e89c-4a9a-8902-4bf571f2c5d8

import Definitions.Def_ThreeSumSharpTail_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false

open ThreeSumSharpTail

/-- The pruned encoding exponent is at most the full-encoding exponent. -/
theorem solution (c : ℝ) (hc : 1 < c) :
    ((c / 2) * entropy (1 / c) + (c - 1) * Real.log 3) / Real.log 4
      ≤ encodingExponent c := by
  have hcpos : 0 < c := by linarith
  have hp : 0 < 1 / c := by positivity
  have hq : 0 < 1 - 1 / c := by
    have hfrac : 1 / c < 1 := by
      rw [div_lt_iff₀ hcpos]
      nlinarith
    linarith
  have hpq : 1 / c + (1 - 1 / c) = 1 := by ring
  have harg1 : (1 : ℝ) / (10 * (1 / c)) = (1 / 10 : ℝ) / (1 / c) := by ring
  have harg2 : (9 : ℝ) / (10 * (1 - 1 / c)) = (9 / 10 : ℝ) / (1 - 1 / c) := by
    field_simp
  have hlog1 : Real.log (1 / (10 * (1 / c))) = -Real.log 10 - Real.log (1 / c) := by
    rw [harg1, Real.log_div (by norm_num : (1 / 10 : ℝ) ≠ 0) (ne_of_gt hp),
      Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (10 : ℝ) ≠ 0),
      Real.log_one]
    ring
  have hlog2 : Real.log (9 / (10 * (1 - 1 / c))) =
      Real.log 9 - Real.log 10 - Real.log (1 - 1 / c) := by
    rw [harg2, Real.log_div (by norm_num : (9 / 10 : ℝ) ≠ 0) (ne_of_gt hq),
      Real.log_div (by norm_num : (9 : ℝ) ≠ 0) (by norm_num : (10 : ℝ) ≠ 0)]
  have hlogle1 : Real.log (1 / (10 * (1 / c))) ≤ 1 / (10 * (1 / c)) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0 : ℝ) < 1) (mul_pos (by norm_num) hp))
  have hlogle2 : Real.log (9 / (10 * (1 - 1 / c))) ≤ 9 / (10 * (1 - 1 / c)) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0 : ℝ) < 9) (mul_pos (by norm_num) hq))
  have hweighted1 := mul_le_mul_of_nonneg_left hlogle1 hp.le
  have hweighted2 := mul_le_mul_of_nonneg_left hlogle2 hq.le
  have hw1' : (1 / c) * (-Real.log 10 - Real.log (1 / c)) ≤ 1 / 10 - 1 / c := by
    calc
      (1 / c) * (-Real.log 10 - Real.log (1 / c))
          = (1 / c) * Real.log (1 / (10 * (1 / c))) := by rw [hlog1]
      _ ≤ (1 / c) * (1 / (10 * (1 / c)) - 1) := hweighted1
      _ = 1 / 10 - 1 / c := by field_simp
  have hw2' : (1 - 1 / c) * (Real.log 9 - Real.log 10 - Real.log (1 - 1 / c))
      ≤ 9 / 10 - (1 - 1 / c) := by
    calc
      (1 - 1 / c) * (Real.log 9 - Real.log 10 - Real.log (1 - 1 / c))
          = (1 - 1 / c) * Real.log (9 / (10 * (1 - 1 / c))) := by rw [hlog2]
      _ ≤ (1 - 1 / c) * (9 / (10 * (1 - 1 / c)) - 1) := hweighted2
      _ = 9 / 10 - (1 - 1 / c) := by
        field_simp [ne_of_gt hcpos, ne_of_gt (sub_pos.mpr hc)]
  have hentropy : entropy (1 / c) + (1 - 1 / c) * Real.log 9 ≤ Real.log 10 := by
    unfold entropy
    nlinarith [hw1', hw2', hpq]
  have hnum : c * entropy (1 / c) + (c - 1) * Real.log 9 ≤ c * Real.log 10 := by
    have hmul := mul_le_mul_of_nonneg_left hentropy hcpos.le
    have hcoeff : c * (1 - 1 / c) = c - 1 := by field_simp
    calc
      c * entropy (1 / c) + (c - 1) * Real.log 9
          = c * (entropy (1 / c) + (1 - 1 / c) * Real.log 9) := by rw [← hcoeff]; ring
      _ ≤ c * Real.log 10 := hmul
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  unfold encodingExponent
  apply (div_le_div_iff_of_pos_right hlog4).2
  nlinarith [hnum, hlog9]

#print axioms solution
