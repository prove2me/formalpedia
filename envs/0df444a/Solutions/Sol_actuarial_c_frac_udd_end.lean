-- Prove2me | solution 1 for actuarial_c_frac_udd_end
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:34.924804+00:00
-- url     : https://prove2.me/submissions/3367b01c-ec46-4f3f-b0a4-57f8a570d903

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_frac_uddSurvival

open ActuarialAssurances.Fractional

theorem solution (p : ℝ) : uddSurvival p 1 = p := by
  simp [uddSurvival]
