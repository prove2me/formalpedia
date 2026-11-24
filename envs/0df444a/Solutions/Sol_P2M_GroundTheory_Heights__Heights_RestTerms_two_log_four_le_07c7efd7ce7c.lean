-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_two_log_four_le_07c7efd7ce7c
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T05:14:35.511864+00:00
-- url     : https://prove2.me/submissions/2c080525-db97-4442-919f-bccbf27a3d1c

import Mathlib


theorem solution : 2 * Real.log 4 ≤ 2.78 := by
  have h : Real.log (4:ℝ) = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  rw [h]; linarith [Real.log_two_lt_d9]
