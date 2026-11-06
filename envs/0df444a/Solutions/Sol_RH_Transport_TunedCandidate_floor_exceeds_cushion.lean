-- Prove2me | solution 1 for RH.Transport.TunedCandidate.floor_exceeds_cushion
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:06:50.895245+00:00
-- url     : https://prove2.me/submissions/da26d02c-23cf-4d7c-a7f3-0689573ecc38

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem solution : cushion < sideMargin .floor := by
  norm_num [cushion, sideMargin, p, b]
