-- Prove2me | solution 1 for WorkbookCorrected.plus_22147
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T05:23:13.413257+00:00
-- url     : https://prove2.me/submissions/3be02c53-cf68-4368-96c9-2da9b20a150a

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum

theorem solution : Real.logb 25 10 = Real.log 10 / Real.log 25 := by
  rfl
