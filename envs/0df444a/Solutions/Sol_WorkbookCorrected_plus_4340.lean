-- Prove2me | solution 1 for WorkbookCorrected.plus_4340
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T04:55:21.676806+00:00
-- url     : https://prove2.me/submissions/c1dcb31e-a8b6-4065-9268-f2c6ff6ce73e

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum

theorem solution : Real.logb 3 (2 ^ 102) = 102 * Real.logb 3 2 := by
  -- Coerce Nat power into Real power
  have h : ((2:ℕ) ^ 102 : ℝ) = (2:ℝ) ^ 102 := by norm_cast
  -- formal statement uses 2 ^ 102 which elaborates as Nat.pow then cast
  simpa [h] using (Real.logb_pow (b := (3:ℝ)) (x := (2:ℝ)) 102)
