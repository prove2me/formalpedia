-- Prove2me | solution 1 for RH.Transport.LocalBounds.goodTailDecay_eq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:07:18.290331+00:00
-- url     : https://prove2.me/submissions/d220798e-aabb-4d05-929c-d07bfcaa5d23

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds
set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section

theorem solution (p : ℝ) :
    goodTailDecay p = -1 - goodCap p := by
  simp only [goodTailDecay, goodCap]
  ring
