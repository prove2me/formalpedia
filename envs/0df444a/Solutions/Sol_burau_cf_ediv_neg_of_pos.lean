-- Prove2me | solution 1 for burau_cf_ediv_neg_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T21:30:00.340361+00:00
-- url     : https://prove2.me/submissions/69e73e08-9903-44df-b086-d2ca8a9e11f2

import Mathlib

/-- Euclidean division of a negated dividend: for `a, b > 0`, `(-a)/b = -⌈a/b⌉ = -((a+b-1)/b)`. -/
theorem solution (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    (-a) / b = -((a + b - 1) / b) := by
  set q := (a + b - 1) / b with hq
  set s := (a + b - 1) % b with hs
  have hbne : b ≠ 0 := ne_of_gt hb
  have hs0 : 0 ≤ s := by rw [hs]; exact Int.emod_nonneg _ hbne
  have hslt : s < b := by
    have h := Int.emod_lt_abs (a + b - 1) hbne
    rwa [abs_of_pos hb] at h
  have hsplit : a + b - 1 = b * q + s := by
    have h := Int.mul_ediv_add_emod (a + b - 1) b
    rw [← hq, ← hs] at h
    linarith
  have hr : b * q - a = b - 1 - s := by linarith
  have hr0 : 0 ≤ b - 1 - s := by omega
  have hrlt : b - 1 - s < b := by omega
  calc (-a) / b = ((b * q - a) + b * (-q)) / b := by
        congr 1
        ring
    _ = (b * q - a) / b + (-q) := by rw [Int.add_mul_ediv_left (b * q - a) (-q) hbne]
    _ = 0 + (-q) := by
          rw [hr, Int.ediv_eq_zero_of_lt_abs hr0 (by rw [abs_of_pos hb]; exact hrlt)]
    _ = -q := by ring
    _ = -((a + b - 1) / b) := by rw [hq]
