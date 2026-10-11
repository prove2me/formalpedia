-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.paid_mixed_lower
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:22:24.310267+00:00
-- url     : https://prove2.me/submissions/509c42fe-6193-4225-bddf-9c16a231fe92

import Theorems.Thm_WeilDefect_RPB108_DNE27Even_theta_bounds
import Theorems.Thm_WeilDefect_RPB108_DNE27Even_lowLower_identity
import Theorems.Thm_WeilDefect_RPB108_paid_young_lower
import Definitions.Def_RPB108_DNE27MixedEnergy_Even
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Even
theorem solution (x y : ℝ) :
    lowLower*x^2+theta*y^2 ≤ nativeLow*x^2-2*mixedUpper*|x*y|+y^2 := by
  rw [lowLower_identity]
  exact paid_young_lower _ _ _ _ _ theta_bounds.2
