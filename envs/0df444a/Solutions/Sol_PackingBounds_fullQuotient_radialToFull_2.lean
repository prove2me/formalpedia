-- Prove2me | solution 2 for PackingBounds.fullQuotient_radialToFull
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:13:36.570993+00:00
-- url     : https://prove2.me/submissions/a5c0b30f-66ae-4bed-a172-4844f33082dc

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap Topology
open PackingBounds


theorem solution {d : ℕ}
    (f : CohnElkies.Admissible d) :
    fullQuotient (radialToFull f) = CohnElkies.quotient f := by
  rfl

