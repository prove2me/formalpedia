-- Prove2me | solution 1 for RH.Transport.TunedCandidate.cushion_pos
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:03:43.920145+00:00
-- url     : https://prove2.me/submissions/64dec544-9d1d-4933-beb4-09a4b5bb4226

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem solution : 0 < cushion := by
  norm_num [cushion]
