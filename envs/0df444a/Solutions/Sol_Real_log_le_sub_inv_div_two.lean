-- Prove2me | solution 1 for Real.log_le_sub_inv_div_two
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-05T18:31:49.344969+00:00
-- url     : https://prove2.me/submissions/80f321d8-e127-47ce-b0ad-c755154fe43b

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

theorem solution {t : ℝ} (ht : 1 ≤ t) :
    Real.log t ≤ (t - 1 / t) / 2 := by
  have ht0 : (0:ℝ) < t := by linarith
  have hx : (0:ℝ) ≤ Real.log t := Real.log_nonneg ht
  have h := (Real.self_le_sinh_iff (x := Real.log t)).mpr hx
  rw [Real.sinh_eq, Real.exp_log ht0, Real.exp_neg, Real.exp_log ht0] at h
  rw [one_div]
  exact h
