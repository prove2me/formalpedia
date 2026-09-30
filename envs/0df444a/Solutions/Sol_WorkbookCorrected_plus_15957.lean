-- Prove2me | solution 1 for WorkbookCorrected.plus_15957
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-30T09:06:05.448232+00:00
-- url     : https://prove2.me/submissions/96e4bb8e-e1fc-403f-9032-4c5e1461e50e

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

theorem solution : Real.logb 5 10 < 3 / 2 := by
  rw [Real.logb]
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  rw [div_lt_iff₀ h5]
  rw [show (10 : ℝ) = 2 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have h45 : Real.log (4 : ℝ) < Real.log 5 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h45
  norm_num at h45 ⊢
  linarith
