-- Prove2me | solution 1 for SpherePacking.Alternative.quotient_eq_of_radialSymmetrizationAverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/6cd3516f-ce91-4f1a-b74e-249ea0a8ddb0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_SpherePacking_Alternative_quotient_eq_of_origin_and_fourier_origin
import Theorems.Thm_SpherePacking_Alternative_radialSymmetrizationAverage_schwartz_zero

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
theorem _root_.solution
    {d : ℕ} {f g : Schwartz d}
    (haverage : ∀ x : Ambient d,
      g x = radialSymmetrizationAverage f x)
    (hfourier : ∀ x : Ambient d,
      (𝓕 g : Schwartz d) x =
        radialSymmetrizationAverage (𝓕 f : Schwartz d) x) :
    quotient g = quotient f := by
  exact quotient_eq_of_origin_and_fourier_origin
    (radialSymmetrizationAverage_schwartz_zero haverage)
    (radialSymmetrizationAverage_fourier_zero hfourier)
end SpherePacking.Alternative
