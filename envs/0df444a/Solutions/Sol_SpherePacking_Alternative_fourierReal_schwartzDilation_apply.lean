-- Prove2me | solution 1 for SpherePacking.Alternative.fourierReal_schwartzDilation_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/a6907b06-ee5a-4bf0-8e36-861ad5141e4c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_Alternative_fourier_schwartzDilation_apply

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
theorem _root_.solution {d : ℕ} (a : ℝ) (ha : 0 < a)
    (f : Schwartz d) (ξ : Ambient d) :
    fourierReal (schwartzDilation a ha.ne' f) ξ =
      (a ^ d)⁻¹ * fourierReal f (a⁻¹ • ξ) := by
  unfold fourierReal
  rw [fourier_schwartzDilation_apply a ha f ξ]
  rw [Complex.smul_re]
  rfl
end SpherePacking.Alternative
