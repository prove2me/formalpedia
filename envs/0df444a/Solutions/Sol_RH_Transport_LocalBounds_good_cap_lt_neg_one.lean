-- Prove2me | solution 1 for RH.Transport.LocalBounds.good_cap_lt_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:56:10.316591+00:00
-- url     : https://prove2.me/submissions/2ce3894b-bede-47b9-af95-f0de9054ebf6

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds

set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section
namespace RH.Transport.LocalBounds
theorem _root_.solution {p : ℝ} (hp : p < 1 / 1000) :
    goodCap p < -1 := by
  dsimp [goodCap]
  linarith
end RH.Transport.LocalBounds
