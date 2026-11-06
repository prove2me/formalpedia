-- Prove2me | solution 2 for RH.Transport.TunedCandidate.width_add_ell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:50.758072+00:00
-- url     : https://prove2.me/submissions/6c836c2c-47b1-46a5-8d5d-f5722d6b3213

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution : width + ell = 1 := by dsimp [width, widthAt]; ring
end RH.Transport.TunedCandidate
