-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.log_product_supermodular
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:15:52.373442+00:00
-- url     : https://prove2.me/submissions/e240d6d7-a3bb-45d6-9473-c15df52102bc

import Mathlib
set_option autoImplicit false

/-- The log of one plus a nonnegative product is strictly supermodular. -/
private theorem strict_log_supermodular (t x x' y y' : ℝ) (ht : 0 < t)
    (hx : 0 ≤ x) (hxx : x < x') (hy : 0 ≤ y) (hyy : y < y') :
    Real.log (1+t*x'*y') + Real.log (1+t*x*y) >
      Real.log (1+t*x'*y) + Real.log (1+t*x*y') := by
  have hxp : 0 ≤ x' := by linarith
  have hyp : 0 ≤ y' := by linarith
  have hp1 : 0 < 1+t*x'*y' := by positivity
  have hp2 : 0 < 1+t*x*y := by positivity
  have hp3 : 0 < 1+t*x'*y := by positivity
  have hp4 : 0 < 1+t*x*y' := by positivity
  rw [← Real.log_mul (ne_of_gt hp1) (ne_of_gt hp2),
      ← Real.log_mul (ne_of_gt hp3) (ne_of_gt hp4)]
  apply Real.log_lt_log (mul_pos hp3 hp4)
  have h := mul_pos ht (mul_pos (sub_pos.mpr hxx) (sub_pos.mpr hyy))
  nlinarith

/-- Weak and strict logarithmic supermodularity. -/
theorem solution (t x x' y y' : ℝ) (ht : 0 ≤ t)
    (hx : 0 ≤ x) (hxx : x ≤ x') (hy : 0 ≤ y) (hyy : y ≤ y') :
    Real.log (1+t*x'*y') + Real.log (1+t*x*y) ≥
      Real.log (1+t*x'*y) + Real.log (1+t*x*y') ∧
    (0 < t → x < x' → y < y' →
      Real.log (1+t*x'*y') + Real.log (1+t*x*y) >
        Real.log (1+t*x'*y) + Real.log (1+t*x*y')) := by
  have hxp : 0 ≤ x' := le_trans hx hxx
  have hyp : 0 ≤ y' := le_trans hy hyy
  have hp1 : 0 < 1+t*x'*y' := by positivity
  have hp2 : 0 < 1+t*x*y := by positivity
  have hp3 : 0 < 1+t*x'*y := by positivity
  have hp4 : 0 < 1+t*x*y' := by positivity
  constructor
  · rw [← Real.log_mul (ne_of_gt hp1) (ne_of_gt hp2),
        ← Real.log_mul (ne_of_gt hp3) (ne_of_gt hp4)]
    apply Real.log_le_log (mul_pos hp3 hp4)
    have h := mul_nonneg ht (mul_nonneg (sub_nonneg.mpr hxx) (sub_nonneg.mpr hyy))
    nlinarith
  · intro ht' hxx' hyy'
    exact strict_log_supermodular t x x' y y' ht' hx hxx' hy hyy'
