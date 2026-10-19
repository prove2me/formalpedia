-- Prove2me | solution 1 for SpherePacking.Alternative.fourierReal_schwartzDilation_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/317863f1-4efd-4833-be57-71ec3f819090

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_Alternative_fourierReal_schwartzDilation_apply

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory
open scoped FourierTransform Real Topology
open SpherePacking SpherePacking.Alternative
namespace SpherePacking.Alternative
theorem _root_.solution {d : ℕ}
    {f : Schwartz d} (hf : ∀ ξ, 0 ≤ fourierReal f ξ)
    (a : ℝ) (ha : 0 < a) (ξ : Ambient d) :
    0 ≤ fourierReal (schwartzDilation a ha.ne' f) ξ := by
  rw [fourierReal_schwartzDilation_apply a ha f ξ]
  exact mul_nonneg (by positivity) (hf _)
end SpherePacking.Alternative
