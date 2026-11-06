-- Prove2me | solution 3 for RH.Transport.SupportedMass.supported_term_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:49:59.991363+00:00
-- url     : https://prove2.me/submissions/2cd6e582-c0f5-4abe-bd11-121b5f45f473

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section

theorem solution {q T : ℝ} (hT : 0 < T) (hq : T ≤ q) :
    q ^ (-2 : ℝ) ≤ T ^ (-(1 / 2 : ℝ)) * q ^ (-(3 / 2 : ℝ)) := by
  have hq0 : 0 < q := lt_of_lt_of_le hT hq
  have h1 : q ^ (-(1 / 2 : ℝ)) ≤ T ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hT hq (by norm_num)
  have h2 : q ^ (-2 : ℝ) = q ^ (-(1 / 2 : ℝ)) * q ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add hq0]; norm_num
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hq0.le _)
