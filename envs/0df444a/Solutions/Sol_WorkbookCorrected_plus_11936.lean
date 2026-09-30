-- Prove2me | solution 1 for WorkbookCorrected.plus_11936
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T05:15:58.054209+00:00
-- url     : https://prove2.me/submissions/80d857f3-05ef-4977-9d56-914d1a4ab66e

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum

theorem solution : Real.logb 5 625 = 4 := by
  have h : (625:ℝ) = (5:ℝ)^4 := by norm_num
  rw [h, Real.logb_pow]
  simpa using (Real.logb_self_eq_one (by norm_num : (1:ℝ) < 5))
