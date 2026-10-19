-- Prove2me | solution 1 for PackingBounds.fullQuotient_radialToFull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/0613d987-fa86-449a-a22f-a206b8644fe0

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
namespace PackingBounds
theorem _root_.solution {d : ℕ}
    (f : CohnElkies.Admissible d) :
    fullQuotient (radialToFull f) = CohnElkies.quotient f := by
  rfl
end PackingBounds
