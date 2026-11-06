-- Prove2me | solution 1 for RH.Transport.TunedCandidate.lowExponent_value
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:06:10.13796+00:00
-- url     : https://prove2.me/submissions/d8da22ff-2dc9-4dcf-9a0a-79e91c4ceb28

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate
set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section

theorem solution : lowExponent = 938614149 / 5000000000 := by
  norm_num [lowExponent, lowExponentAt, ell, Geometry.ell, p, b, lxAt]
