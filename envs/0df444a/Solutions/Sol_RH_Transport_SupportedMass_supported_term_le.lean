-- Prove2me | solution 1 for RH.Transport.SupportedMass.supported_term_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:59:02.938119+00:00
-- url     : https://prove2.me/submissions/9efb0394-46eb-4efb-bf5f-6c32bdb870b5

import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false

noncomputable section

theorem solution {q T : ℝ} (hT : 0 < T) (hq : T ≤ q) :
    q ^ (-2 : ℝ) ≤ T ^ (-(1 / 2 : ℝ)) * q ^ (-(3 / 2 : ℝ)) := by
  have hq_pos : 0 < q := hT.trans_le hq
  have hpow : q ^ (-(1 / 2 : ℝ)) ≤ T ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hT hq (by norm_num)
  rw [show (-2 : ℝ) = -(1 / 2 : ℝ) + -(3 / 2 : ℝ) by norm_num,
    Real.rpow_add hq_pos]
  exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hq_pos.le _)
