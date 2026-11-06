-- Prove2me | solution 2 for RH.Transport.LocalBounds.goodTailDecay_gt_four_fifths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:26.127164+00:00
-- url     : https://prove2.me/submissions/68b72bed-6528-4f92-8f2d-66f14d07f312

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds

set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
namespace RH.Transport.LocalBounds
theorem _root_.solution {p : ℝ} (hp : p < 1 / 1000) :
    (4 / 5 : ℝ) < goodTailDecay p := by
  dsimp [goodTailDecay]
  linarith
end RH.Transport.LocalBounds
