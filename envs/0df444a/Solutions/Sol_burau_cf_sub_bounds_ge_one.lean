-- Prove2me | solution 1 for burau_cf_sub_bounds_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T21:41:39.734281+00:00
-- url     : https://prove2.me/submissions/22c2975d-ab38-4db6-8fdc-4c9e021c2b7d

import Mathlib

/-- If `1 ≤ b/a` with `a > 0` then `a ≤ b`, i.e. `0 ≤ b - a < b`. -/
theorem solution (a b : ℤ) (ha : 0 < a) (h : 1 ≤ b / a) : 0 ≤ b - a ∧ b - a < b := by
  have hd := Int.mul_ediv_add_emod b a
  have h1 : 0 ≤ b % a := Int.emod_nonneg b (ne_of_gt ha)
  have hk : a * 1 ≤ a * (b / a) := Int.mul_le_mul_of_nonneg_left h ha.le
  constructor <;> omega
