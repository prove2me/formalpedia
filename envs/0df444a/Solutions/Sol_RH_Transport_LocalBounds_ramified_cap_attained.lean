-- Prove2me | solution 1 for RH.Transport.LocalBounds.ramified_cap_attained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:24.258111+00:00
-- url     : https://prove2.me/submissions/6a830baa-9327-4305-9d6a-59d58feb070c

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds

set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
namespace RH.Transport.LocalBounds
theorem _root_.solution (p : ℝ) :
    ramifiedPower .strictFamily (boundary p) (19 / 20) (33 / 200) =
      ramifiedCap p := by
  dsimp [ramifiedPower, ramifiedCap, boundary]
  ring
end RH.Transport.LocalBounds
