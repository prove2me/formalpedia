-- Prove2me | solution 1 for burau_cf_emod_neg_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T21:37:14.10309+00:00
-- url     : https://prove2.me/submissions/9a917c2a-cbfc-4a29-b605-40f68762df8c

import Mathlib

/-- Euclidean remainder of a negated dividend: for `a, b > 0`,
`(-a) % b = b * ((a+b-1)/b) - a`. -/
theorem solution (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    (-a) % b = b * ((a + b - 1) / b) - a := by
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
  calc (-a) % b = ((b * q - a) + b * (-q)) % b := by
        congr 2
        ring
    _ = (b * q - a) % b := by rw [Int.add_mul_emod_self_left]
    _ = b - 1 - s := by
          rw [hr]
          exact Int.emod_eq_of_lt hr0 hrlt
    _ = b * q - a := by linarith
    _ = b * ((a + b - 1) / b) - a := by rw [hq]
