-- Prove2me | solution 1 for WorkbookCorrected.plus_51735
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:47:58.975677+00:00
-- url     : https://prove2.me/submissions/36cfc42f-8e22-4344-95e5-3856e08c86cb

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : (Real.sqrt 3 ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = Real.sqrt 9 := by
  rw [← Real.rpow_mul (Real.sqrt_nonneg 3),
    Real.mul_self_sqrt (by norm_num : 0 ≤ (2 : ℝ)), Real.rpow_two,
    Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : 0 ≤ (3 : ℝ))]
