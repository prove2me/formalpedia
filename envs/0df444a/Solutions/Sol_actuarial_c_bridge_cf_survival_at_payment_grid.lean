-- Prove2me | solution 1 for actuarial_c_bridge_cf_survival_at_payment_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-14T06:51:28.001424+00:00
-- url     : https://prove2.me/submissions/d24ddbb8-69ad-44cf-9aee-3cdfefd9dadc

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_cont_fractionalTime
import Definitions.Def_actuarial_c_frac_cfSurvival
import Definitions.Def_actuarial_c_frac_cfHalf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAssurances.Fractional

theorem solution (p : ℝ) (hp : 0 < p) :
    cfSurvival p (ActuarialAssurances.Continuous.fractionalTime 2 1) =
      cfHalf p := by
  have hgrid :
      ActuarialAssurances.Continuous.fractionalTime 2 1 = (1 / 2 : ℝ) := by
    norm_num [ActuarialAssurances.Continuous.fractionalTime]
  rw [hgrid]
  unfold cfSurvival cfHalf
  have he : (Real.exp (Real.log p * (1 / 2 : ℝ))) ^ 2 = p := by
    rw [pow_two, ← Real.exp_add]
    have harg :
        Real.log p * (1 / 2 : ℝ) + Real.log p * (1 / 2 : ℝ) =
          Real.log p := by ring
    rw [harg, Real.exp_log hp]
  have hs : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt (le_of_lt hp)
  have hnon1 : 0 ≤ Real.exp (Real.log p * (1 / 2 : ℝ)) :=
    le_of_lt (Real.exp_pos _)
  have hnon2 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  nlinarith [sq_nonneg (Real.exp (Real.log p * (1 / 2 : ℝ)) -
    Real.sqrt p)]
