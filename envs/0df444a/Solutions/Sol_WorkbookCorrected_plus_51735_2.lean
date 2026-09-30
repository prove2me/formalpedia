-- Prove2me | solution 2 for WorkbookCorrected.plus_51735
-- status  : ACCEPTED   (prove)
-- author  : @yerui
-- created : 2026-09-30T05:50:45.420793+00:00
-- url     : https://prove2.me/submissions/77c16e12-e2bf-4a38-9c7b-a9b74f3b9dc8

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

theorem solution : (Real.sqrt 3 ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = Real.sqrt 9 := by
  rw [← Real.rpow_mul (Real.sqrt_nonneg 3)]
  rw [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [Real.rpow_two]
  rw [show Real.sqrt 9 = 3 by
        rw [show (9:ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
