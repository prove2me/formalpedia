-- Prove2me | solution 1 for actuarial_c_bridge_force_survival_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:53:46.42435+00:00
-- url     : https://prove2.me/submissions/52ec9483-85f8-459a-9514-ccae15e14459

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_c_frac_mortalityForce
import Definitions.Def_actuarial_c_frac_cfSurvival

open ActuarialAssurances.Fractional


theorem solution (p u : ℝ) (hp : 0 < p) :
    cfSurvival p u = Real.exp (-mortalityForce p * u) := by
  unfold cfSurvival mortalityForce
  congr 1; ring

