-- Prove2me | solution 1 for RH.Transport.TunedCandidate.central_remaining_value
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:08:13.859492+00:00
-- url     : https://prove2.me/submissions/b6769d9d-e5d3-4d47-a344-802167cdaa91

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem solution : cushion - 2 * zeta = 3 / 4000000000000 := by
  norm_num [cushion, zeta]
