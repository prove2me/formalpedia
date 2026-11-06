-- Prove2me | solution 2 for RH.Transport.Candidate.intermediate_exceeds_cushion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:11.960131+00:00
-- url     : https://prove2.me/submissions/5c7c1f2a-d115-40fc-8917-d1b1f3033af7

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.Candidate
theorem _root_.solution :
    cushion < sideMargin .intermediate := by
  norm_num [cushion, sideMargin, p]
end RH.Transport.Candidate
