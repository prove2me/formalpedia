-- Prove2me | solution 1 for TaoFivePrimes.logarithmic_counting_main_increment
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:46:04.414907+00:00
-- url     : https://prove2.me/submissions/9408bfef-a6a1-4fa2-883b-acec7b274abe

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem solution (H t c : ℝ) (hH : 0 < H) (hHt : H ≤ t) (hc : 0 < c) :
    t/c * (Real.log (t/c)-1) - H/c * (Real.log (H/c)-1) ≤
      (t-H)/c * Real.log (t/c) := by
  have ht : 0 < t := lt_of_lt_of_le hH hHt
  have hlog := Real.log_le_sub_one_of_pos (div_pos ht hH)
  have hmul : H * Real.log (t/H) ≤ t-H := by
    have hh := mul_le_mul_of_nonneg_left hlog hH.le
    have he : H * (t/H-1) = t-H := by field_simp
    linarith
  have hdiff : Real.log (t/c)-Real.log (H/c) = Real.log (t/H) := by
    rw [Real.log_div ht.ne' hc.ne', Real.log_div hH.ne' hc.ne',
      Real.log_div ht.ne' hH.ne']
    ring
  have hbound : H * (Real.log (t/c)-Real.log (H/c)) ≤ t-H := by
    rw [hdiff]
    exact hmul
  have hnum : t * (Real.log (t/c)-1) - H * (Real.log (H/c)-1) ≤
      (t-H) * Real.log (t/c) := by
    nlinarith only [hbound]
  have hleft : t/c * (Real.log (t/c)-1) - H/c * (Real.log (H/c)-1) =
      (t*(Real.log (t/c)-1)-H*(Real.log (H/c)-1))/c := by ring
  have hright : (t-H)/c * Real.log (t/c) = ((t-H)*Real.log (t/c))/c := by ring
  rw [hleft,hright]
  exact div_le_div_of_nonneg_right hnum hc.le
