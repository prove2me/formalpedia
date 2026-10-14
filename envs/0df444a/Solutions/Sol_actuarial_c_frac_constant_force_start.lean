-- Prove2me | solution 1 for actuarial_c_frac_constant_force_start
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:35.197101+00:00
-- url     : https://prove2.me/submissions/356456e0-3b8e-43b8-aa6f-ac464b91ff65

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_frac_cfSurvival

open ActuarialAssurances.Fractional

theorem solution (p : ℝ) : cfSurvival p 0 = 1 := by
  simp [cfSurvival]
