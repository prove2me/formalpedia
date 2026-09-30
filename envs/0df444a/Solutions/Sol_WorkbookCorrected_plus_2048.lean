-- Prove2me | solution 1 for WorkbookCorrected.plus_2048
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-30T09:49:59.204239+00:00
-- url     : https://prove2.me/submissions/062863b9-c403-4715-b4cb-a754e53bb839

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

theorem solution :
    (2:ℝ) ^ (Real.logb 2 5 - 2) =
      (2:ℝ) ^ (Real.logb 2 5) / (2:ℝ) ^ 2 := by
  rw [Real.rpow_sub (by norm_num), Real.rpow_two]
