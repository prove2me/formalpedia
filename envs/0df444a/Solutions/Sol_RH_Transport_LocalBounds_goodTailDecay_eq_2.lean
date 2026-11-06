-- Prove2me | solution 2 for RH.Transport.LocalBounds.goodTailDecay_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:25.526482+00:00
-- url     : https://prove2.me/submissions/d6dbd540-e278-4288-89fd-cd4ddaf4dd0f

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds

set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
namespace RH.Transport.LocalBounds
theorem _root_.solution (p : ℝ) :
    goodTailDecay p = -1 - goodCap p := by
  dsimp [goodTailDecay, goodCap]
  ring
end RH.Transport.LocalBounds
