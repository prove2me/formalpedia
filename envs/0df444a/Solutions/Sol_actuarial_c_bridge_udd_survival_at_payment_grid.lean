-- Prove2me | solution 1 for actuarial_c_bridge_udd_survival_at_payment_grid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:50:04.755969+00:00
-- url     : https://prove2.me/submissions/ea9dc357-754e-4cce-9d93-eb960f9b8fc9

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_c_cont_fractionalTime
import Definitions.Def_actuarial_c_frac_uddSurvival
import Definitions.Def_actuarial_c_frac_uddHalf

open ActuarialAssurances.Fractional


theorem solution (p : ℝ) :
    uddSurvival p (ActuarialAssurances.Continuous.fractionalTime 2 1) =
      uddHalf p := by
  simp [ActuarialAssurances.Continuous.fractionalTime, ActuarialAssurances.Fractional.uddHalf, ActuarialAssurances.Fractional.uddSurvival, Finset.sum_add_distrib, Finset.mul_sum, mul_add, add_mul]; ring_nf

