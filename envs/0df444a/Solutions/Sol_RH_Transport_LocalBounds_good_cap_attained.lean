-- Prove2me | solution 1 for RH.Transport.LocalBounds.good_cap_attained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:23.643548+00:00
-- url     : https://prove2.me/submissions/b01983ce-065c-4469-8763-846b514a072a

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds

set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
namespace RH.Transport.LocalBounds
theorem _root_.solution (p : ℝ) :
    goodPower .strictFamily (boundary p) (19 / 20) (33 / 200) =
      goodCap p := by
  dsimp [goodPower, goodCap, boundary]
  ring
end RH.Transport.LocalBounds
