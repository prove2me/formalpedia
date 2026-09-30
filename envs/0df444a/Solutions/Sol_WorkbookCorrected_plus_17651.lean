-- Prove2me | solution 1 for WorkbookCorrected.plus_17651
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T04:48:13.32603+00:00
-- url     : https://prove2.me/submissions/2a848158-4bf9-4ccf-9669-99c986d47de9

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum

theorem solution : Real.logb 3 5 + Real.logb 3 6 - Real.logb 3 10 = 1 := by
  have hmul := Real.logb_mul (b := (3:ℝ)) (by norm_num : (5:ℝ) ≠ 0) (by norm_num : (6:ℝ) ≠ 0)
  rw [← hmul]
  rw [show (5:ℝ) * 6 = 30 by norm_num]
  have hdiv := Real.logb_div (b := (3:ℝ)) (by norm_num : (30:ℝ) ≠ 0) (by norm_num : (10:ℝ) ≠ 0)
  rw [← hdiv]
  rw [show (30:ℝ) / 10 = 3 by norm_num]
  exact Real.logb_self_eq_one (by norm_num : (1:ℝ) < 3)
