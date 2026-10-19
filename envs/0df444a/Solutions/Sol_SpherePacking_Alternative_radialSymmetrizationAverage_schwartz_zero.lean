-- Prove2me | solution 1 for SpherePacking.Alternative.radialSymmetrizationAverage_schwartz_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/dbb189db-4a28-47fa-b2ee-4a64dff11808

import Mathlib
import Definitions.Def_SpherePacking

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
      g x = radialSymmetrizationAverage f x) :
    g 0 = f 0 := by
  rw [haverage 0, radialSymmetrizationAverage_zero]
end SpherePacking.Alternative
