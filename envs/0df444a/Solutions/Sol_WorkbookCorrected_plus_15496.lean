-- Prove2me | solution 1 for WorkbookCorrected.plus_15496
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-30T09:08:00.100983+00:00
-- url     : https://prove2.me/submissions/2be5d0e2-3fc5-43e9-a7ea-cd11d051f00b

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution : 1 + Real.sqrt 6 > Real.sqrt 2 := by
  have h1 : (1:ℝ) < Real.sqrt 6 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h2 : Real.sqrt 2 < (2:ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith
