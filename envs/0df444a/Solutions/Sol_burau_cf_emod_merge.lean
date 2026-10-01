-- Prove2me | solution 1 for burau_cf_emod_merge
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T21:44:23.861976+00:00
-- url     : https://prove2.me/submissions/ff000f62-1ced-47a3-9582-bb76425f3666

import Mathlib

/-- Adding `b - a` to `a` does not change the remainder modulo `b - a`: the arithmetic content of the
merging of the two Euclidean descents used in the continued-fraction analysis. -/
theorem solution (a b : ℤ) : b % (b - a) = a % (b - a) := by
  have h : b = a + (b - a) * 1 := by ring
  nth_rewrite 1 [h]
  rw [Int.add_mul_emod_self_left]
