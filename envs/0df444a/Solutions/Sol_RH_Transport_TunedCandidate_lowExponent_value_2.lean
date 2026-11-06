-- Prove2me | solution 2 for RH.Transport.TunedCandidate.lowExponent_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:03.384128+00:00
-- url     : https://prove2.me/submissions/509434b7-71d1-4f60-b1c6-78dcf35f08f0

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution : lowExponent = 938614149 / 5000000000 := by
  norm_num [lowExponent, lowExponentAt, lxAt, ell, Geometry.ell, b, p]
end RH.Transport.TunedCandidate
