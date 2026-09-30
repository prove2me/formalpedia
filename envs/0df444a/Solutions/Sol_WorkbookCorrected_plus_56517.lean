-- Prove2me | solution 1 for WorkbookCorrected.plus_56517
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-30T09:08:21.419526+00:00
-- url     : https://prove2.me/submissions/cda3a127-0717-428e-858a-3666617f37f3

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution : Real.log (11/10:ℝ) < 1 / 1155 ^ (1/3) := by
  have e : (1/3 : ℕ) = 0 := by decide
  rw [e, pow_zero, div_one]
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h2 : (2:ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (show (1:ℝ) ≠ 0 by norm_num)
    linarith
  linarith
