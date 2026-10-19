-- Prove2me | solution 1 for actuarial_c_frac_constant_force_end
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:02:02.846454+00:00
-- url     : https://prove2.me/submissions/ae781186-e6a0-41f1-ace7-4da856a6964a

import Mathlib
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_frac_cfSurvival

open ActuarialAssurances.Fractional



theorem solution (p : ℝ) (hp : 0 < p) :
    cfSurvival p 1 = p := by
  unfold cfSurvival; rw [mul_one, Real.exp_log hp]

