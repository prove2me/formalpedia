-- Prove2me | solution 2 for RH.Transport.LocalBounds.goodTailDecay_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:26.728471+00:00
-- url     : https://prove2.me/submissions/891244be-f8e2-4cf6-95c6-8a9472c7b9a3

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds

set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
namespace RH.Transport.LocalBounds
theorem _root_.solution (p : ℝ) :
    goodTailDecay p - 4 / 5 = 3 / 200 - p / 4 := by
  dsimp [goodTailDecay]
  ring
end RH.Transport.LocalBounds
