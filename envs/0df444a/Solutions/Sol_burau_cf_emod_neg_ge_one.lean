-- Prove2me | solution 1 for burau_cf_emod_neg_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T21:59:08.226963+00:00
-- url     : https://prove2.me/submissions/a589ffcb-9c4f-4207-92fb-88ec410ee56b

import Mathlib

/-- First step of the `-1/x` rule in the `b/a ≥ 1` range: `(-a) % b = b - a`. -/
theorem solution (a b : ℤ) (ha : 0 < a) (h : 1 ≤ b / a) : (-a) % b = b - a := by
  have hd := Int.mul_ediv_add_emod b a
  have h1 : 0 ≤ b % a := Int.emod_nonneg b (ne_of_gt ha)
  have hk : a * 1 ≤ a * (b / a) := Int.mul_le_mul_of_nonneg_left h ha.le
  have hle : 0 ≤ b - a := by omega
  have hlt : b - a < b := by omega
  calc (-a) % b = ((b - a) + b * (-1)) % b := by
        congr 2
        ring
    _ = (b - a) % b := by rw [Int.add_mul_emod_self_left]
    _ = b - a := Int.emod_eq_of_lt hle hlt
