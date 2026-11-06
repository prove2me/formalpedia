-- Prove2me | solution 1 for RH.Transport.TunedCandidate.intermediateExponent_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:57:58.033081+00:00
-- url     : https://prove2.me/submissions/c4d10d1b-58a9-4a94-aeae-9bbebb62e251

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
import Definitions.Def_Transport_TunedCandidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.TunedCandidate
theorem _root_.solution (δ x : ℝ) :
    intermediateExponent δ x =
      -41270920211 / 187500000000 +
        (2662873553 / 15000000000) * δ +
        (625643953 / 3750000000) * δ * x := by
  norm_num [intermediateExponent, B, boundaryAt, h, hAt, ly, lyAt,
    ell, Geometry.ell, p, b]
  ring
end RH.Transport.TunedCandidate
