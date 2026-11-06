-- Prove2me | solution 2 for RH.Transport.TunedCandidate.central_remaining_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:06.239488+00:00
-- url     : https://prove2.me/submissions/4933b477-717d-40f7-97f0-a86b353118ab

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution : 0 < cushion - 2 * zeta := by
  norm_num [cushion, zeta]
end RH.Transport.TunedCandidate
