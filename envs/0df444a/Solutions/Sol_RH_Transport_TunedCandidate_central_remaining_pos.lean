-- Prove2me | solution 1 for RH.Transport.TunedCandidate.central_remaining_pos
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:06:02.594688+00:00
-- url     : https://prove2.me/submissions/ca6e3f11-d6bd-471d-b9a5-b5d3fb4d2065

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem solution : 0 < cushion - 2 * zeta := by
  norm_num [cushion, zeta]
