-- Prove2me | solution 1 for WorkbookCorrected.plus_27001
-- status  : ACCEPTED   (disprove)
-- author  : @Sneed
-- created : 2026-09-30T09:36:51.065987+00:00
-- url     : https://prove2.me/submissions/cd214dcd-bd6d-4ad6-9b27-78495f3b63d2

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum

theorem solution :
    ¬ (Real.logb 5 (25) + Real.logb 5 (125) = 4) := by
  intro h
  have h5 : Real.logb 5 5 = 1 := by
    simpa using (Real.logb_self_eq_one (show (1 : ℝ) < 5 by norm_num))
  have h25 : Real.logb 5 25 = 2 := by
    calc
      Real.logb 5 25 = Real.logb 5 ((5 : ℝ) ^ 2) := by norm_num
      _ = (2 : ℕ) * Real.logb 5 5 := Real.logb_pow 5 5 2
      _ = 2 := by rw [h5]; norm_num
  have h125 : Real.logb 5 125 = 3 := by
    calc
      Real.logb 5 125 = Real.logb 5 ((5 : ℝ) ^ 3) := by norm_num
      _ = (3 : ℕ) * Real.logb 5 5 := Real.logb_pow 5 5 3
      _ = 3 := by rw [h5]; norm_num
  rw [h25, h125] at h
  norm_num at h
