-- Prove2me | solution 1 for actuarial_c_frac_udd_half_agrees_with_time_model
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:02:27.93397+00:00
-- url     : https://prove2.me/submissions/c46cb828-0b82-4324-90c3-fd421043b591

import Mathlib
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_frac_uddHalf
import Definitions.Def_actuarial_c_frac_uddSurvival

open ActuarialAssurances.Fractional



theorem solution (p : ℝ) :
    uddSurvival p (1 / 2) = uddHalf p := by
  unfold uddSurvival uddHalf; ring

