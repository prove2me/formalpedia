-- Prove2me | solution 1 for WorkbookCorrected.plus_1247
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T06:02:42.874804+00:00
-- url     : https://prove2.me/submissions/b1480dac-3b63-40b9-a588-edc55ccaac0a

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution : (7:ℝ) = (10:ℝ) ^ Real.logb 10 7 := by
  norm_num
