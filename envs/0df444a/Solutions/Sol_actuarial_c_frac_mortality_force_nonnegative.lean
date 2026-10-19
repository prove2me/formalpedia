-- Prove2me | solution 1 for actuarial_c_frac_mortality_force_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:02:20.778685+00:00
-- url     : https://prove2.me/submissions/64df2959-a323-468b-815e-bb9d681f4fa5

import Mathlib
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_frac_mortalityForce

open ActuarialAssurances.Fractional



theorem solution (p : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    0 ≤ mortalityForce p := by
  unfold mortalityForce; have := Real.log_nonpos hp.le hp1; linarith

