-- Prove2me | solution 1 for RH.Transport.LocalBounds.goodTailDecay_gt_four_fifths
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:10:10.907215+00:00
-- url     : https://prove2.me/submissions/d105be63-4a58-4ca5-a789-5909f73d5e9c

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds
set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section

theorem solution {p : ℝ} (hp : p < 1 / 1000) :
    (4 / 5 : ℝ) < goodTailDecay p := by
  unfold goodTailDecay
  linarith
