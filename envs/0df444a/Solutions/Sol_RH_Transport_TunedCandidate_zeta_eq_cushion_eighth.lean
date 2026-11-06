-- Prove2me | solution 1 for RH.Transport.TunedCandidate.zeta_eq_cushion_eighth
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:07:03.188912+00:00
-- url     : https://prove2.me/submissions/ce00602f-0843-442f-b462-3f77e5fc1d79

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem solution : zeta = cushion / 8 := by
  norm_num [zeta, cushion]
