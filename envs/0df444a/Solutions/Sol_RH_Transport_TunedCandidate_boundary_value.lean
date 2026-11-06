-- Prove2me | solution 1 for RH.Transport.TunedCandidate.boundary_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:57:25.905207+00:00
-- url     : https://prove2.me/submissions/143a6499-8577-41fb-afc1-a0a016d2f38f

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution : B = 4374785349 / 5000000000 := by
  norm_num [B, boundaryAt, ell, Geometry.ell, p]
end RH.Transport.TunedCandidate
