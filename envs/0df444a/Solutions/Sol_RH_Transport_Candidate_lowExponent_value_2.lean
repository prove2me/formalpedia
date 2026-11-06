-- Prove2me | solution 2 for RH.Transport.Candidate.lowExponent_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:17:56.549643+00:00
-- url     : https://prove2.me/submissions/9a03fc88-d7f8-4a8f-a8f9-c90e15f05389

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.Candidate
theorem _root_.solution :
    lowExponent p = 299931521 / 1600000000 := by
  norm_num [lowExponent, lx, b, p]
end RH.Transport.Candidate
