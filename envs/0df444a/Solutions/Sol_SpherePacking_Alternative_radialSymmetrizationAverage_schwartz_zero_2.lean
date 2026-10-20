-- Prove2me | solution 2 for SpherePacking.Alternative.radialSymmetrizationAverage_schwartz_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:27:57.500285+00:00
-- url     : https://prove2.me/submissions/249732de-10b0-4aa1-89dd-604ec2750900

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


theorem solution
    {d : ℕ} {f g : Schwartz d}
    (haverage : ∀ x : Ambient d,
      g x = radialSymmetrizationAverage f x) :
    g 0 = f 0 := by
  rw [haverage, radialSymmetrizationAverage_zero]

