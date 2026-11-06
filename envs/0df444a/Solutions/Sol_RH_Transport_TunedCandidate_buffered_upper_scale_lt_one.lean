-- Prove2me | solution 1 for RH.Transport.TunedCandidate.buffered_upper_scale_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:05:20.930068+00:00
-- url     : https://prove2.me/submissions/89b99a0a-66e0-44ff-8b0b-ceafeb99998a

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem solution : h + zeta < 1 := by
  norm_num [h, hAt, ell, Geometry.ell, p, b, zeta]
