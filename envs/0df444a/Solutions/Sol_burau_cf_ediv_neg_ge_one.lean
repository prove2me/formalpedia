-- Prove2me | solution 1 for burau_cf_ediv_neg_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T21:48:11.306435+00:00
-- url     : https://prove2.me/submissions/1e08896b-f0b6-4089-a032-2573504f9070

import Mathlib

/-- First step of the `-1/x` rule in the `b/a ≥ 1` range: `(-a)/b = -1`. -/
theorem solution (a b : ℤ) (ha : 0 < a) (h : 1 ≤ b / a) : (-a) / b = -1 := by
  have hd := Int.mul_ediv_add_emod b a
  have h1 : 0 ≤ b % a := Int.emod_nonneg b (ne_of_gt ha)
  have hk : a * 1 ≤ a * (b / a) := Int.mul_le_mul_of_nonneg_left h ha.le
  have hle : 0 ≤ b - a := by omega
  have hlt : b - a < b := by omega
  have hb : b ≠ 0 := by omega
  have hlt' : b - a < |b| := by
    rw [abs_of_pos (by omega : (0 : ℤ) < b)]
    exact hlt
  calc (-a) / b = ((b - a) + b * (-1)) / b := by
        congr 1
        ring
    _ = (b - a) / b + (-1) := by rw [Int.add_mul_ediv_left (b - a) (-1) hb]
    _ = 0 + (-1) := by rw [Int.ediv_eq_zero_of_lt_abs hle hlt']
    _ = -1 := by ring
