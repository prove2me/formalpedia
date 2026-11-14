-- Prove2me | solution 1 for PGDRevision20261113.rational_scale_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T09:22:42.136617+00:00
-- url     : https://prove2.me/submissions/fe38f342-764e-4781-9150-1e3e430059b6

import Definitions.Def_PGDRevision20261113_NumericalCertificates
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

open PGDRevision20261113

theorem solution : RationalScaleEnclosureClaim := by
  intro p phat b hp hphat hb hb1 hlog
  have hr : 0 < p / phat := div_pos hp hphat
  have hbounds := abs_le.mp hlog
  have hlo := Real.log_le_sub_one_of_pos hr
  have hhi := Real.log_le_sub_one_of_pos (inv_pos.mpr hr)
  rw [Real.log_inv] at hhi
  have hlower : 1 - b ≤ p / phat := by linarith
  have hinverse : 1 - b ≤ (p / phat)⁻¹ := by linarith
  have hproduct : (1 - b) * (p / phat) ≤ 1 := by
    calc
      (1 - b) * (p / phat) ≤ (p / phat)⁻¹ * (p / phat) :=
        mul_le_mul_of_nonneg_right hinverse hr.le
      _ = 1 := inv_mul_cancel₀ hr.ne'
  constructor
  · have h := (le_div_iff₀ hphat).mp hlower
    simpa [mul_comm] using h
  · apply (le_div_iff₀ (by linarith : 0 < 1 - b)).mpr
    calc
      p * (1 - b) = ((1 - b) * (p / phat)) * phat := by
        rw [mul_assoc, div_mul_cancel₀ _ hphat.ne']
        exact mul_comm _ _
      _ ≤ 1 * phat := mul_le_mul_of_nonneg_right hproduct hphat.le
      _ = phat := one_mul _
