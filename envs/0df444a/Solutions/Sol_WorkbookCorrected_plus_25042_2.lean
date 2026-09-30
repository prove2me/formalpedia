-- Prove2me | solution 2 for WorkbookCorrected.plus_25042
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T09:49:10.583986+00:00
-- url     : https://prove2.me/submissions/9e3f09c6-35ca-43d0-bc5c-e669f5a8e6c8

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum

theorem solution : Real.logb 2 (Real.logb 4 16) = 1 := by
  have h16 : Real.logb (4:ℝ) 16 = 2 := by
    have h : (16:ℝ) = (4:ℝ)^2 := by norm_num
    rw [h, Real.logb_pow]
    simpa using (Real.logb_self_eq_one (by norm_num : (1:ℝ) < 4))
  rw [h16]
  simpa using (Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2))
