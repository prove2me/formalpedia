-- Prove2me | solution 1 for RH.Transport.LocalBounds.goodTailDecay_margin
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:09:14.668097+00:00
-- url     : https://prove2.me/submissions/56ee79d2-d4f6-4488-a6eb-727e0c41661e

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds
set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section

theorem solution (p : ℝ) :
    goodTailDecay p - 4 / 5 = 3 / 200 - p / 4 := by
  unfold goodTailDecay
  ring
