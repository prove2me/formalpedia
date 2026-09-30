-- Prove2me | solution 1 for WorkbookCorrected.plus_5951
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T08:06:18.368563+00:00
-- url     : https://prove2.me/submissions/3bc68732-05db-410d-8ded-4985da6a90f6

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

theorem solution : (Real.log (Real.sqrt 3 + 1) - Real.log 2) = Real.log ((Real.sqrt 3 + 1) / 2) := by
  have hA : Real.sqrt 3 + 1 ≠ 0 := by
    have : (0:ℝ) < Real.sqrt 3 + 1 := by positivity
    exact ne_of_gt this
  have hB : (2:ℝ) ≠ 0 := by norm_num
  exact (Real.log_div hA hB).symm
