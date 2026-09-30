-- Prove2me | solution 1 for WorkbookCorrected.plus_18935
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T08:53:45.87299+00:00
-- url     : https://prove2.me/submissions/fd078859-28db-4626-86a4-931cc9f2bbbe

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum

theorem solution :
    (Real.logb 2 (4 * 251)) / (Real.logb 2 (2 * 5)) =
      (2 + Real.logb 2 251) / (1 + Real.logb 2 5) := by
  have h4 : Real.logb (2 : ℝ) 4 = 2 := by
    have h : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
    rw [h, Real.logb_pow]
    simpa using (Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2))
  have hnum : Real.logb (2 : ℝ) (4 * 251) = 2 + Real.logb 2 251 := by
    have hmul := Real.logb_mul (b := (2 : ℝ)) (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (251 : ℝ) ≠ 0)
    rw [hmul, h4]
  have hden : Real.logb (2 : ℝ) (2 * 5) = 1 + Real.logb 2 5 := by
    have hmul := Real.logb_mul (b := (2 : ℝ)) (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (5 : ℝ) ≠ 0)
    rw [hmul, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  rw [hnum, hden]
