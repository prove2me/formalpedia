-- Prove2me | solution 1 for WorkbookCorrected.plus_76506
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T06:06:31.859798+00:00
-- url     : https://prove2.me/submissions/ab7d5664-89cb-4ddc-ac97-dd399ffaee29

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum

theorem solution : (Real.log (11 / 2) - Real.log 2) = Real.log (11 / 4) := by
  have hp : (0:ℝ) < 11/2 := by norm_num
  have hq : (0:ℝ) < 2 := by norm_num
  have hq0 : (2:ℝ) ≠ 0 := by norm_num
  rw [← Real.log_div (ne_of_gt hp) hq0]
  norm_num
