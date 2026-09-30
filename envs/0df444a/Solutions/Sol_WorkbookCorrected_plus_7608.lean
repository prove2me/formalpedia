-- Prove2me | solution 1 for WorkbookCorrected.plus_7608
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T05:20:21.856226+00:00
-- url     : https://prove2.me/submissions/eeebba63-6554-44cb-bc8b-e7649e75bc31

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum

theorem solution : Real.logb 6 2 + Real.logb 6 3 = 1 := by
  have h := Real.logb_mul (b:=(6:ℝ)) (by norm_num : (2:ℝ)≠0) (by norm_num : (3:ℝ)≠0)
  rw [← h]
  rw [show (2:ℝ)*3 = 6 by norm_num]
  exact Real.logb_self_eq_one (by norm_num)
