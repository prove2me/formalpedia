-- Prove2me | solution 1 for actuarial_c_frac_udd_start
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:34.971841+00:00
-- url     : https://prove2.me/submissions/d287da83-3c25-48d0-a0d3-e85bb79e4061

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_frac_uddSurvival

open ActuarialAssurances.Fractional

theorem solution (p : ℝ) : uddSurvival p 0 = 1 := by
  simp [uddSurvival]
