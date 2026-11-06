-- Prove2me | solution 1 for RH.Transport.TunedCandidate.small_exceeds_cushion
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:07:30.444194+00:00
-- url     : https://prove2.me/submissions/fff123b9-b989-4f0b-86cb-36a6777fcb9f

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem solution : cushion < sideMargin .small := by
  norm_num [cushion, sideMargin, ly, h, lyAt, hAt, ell, Geometry.ell, b, p]
