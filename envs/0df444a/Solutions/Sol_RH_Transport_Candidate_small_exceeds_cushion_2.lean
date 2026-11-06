-- Prove2me | solution 2 for RH.Transport.Candidate.small_exceeds_cushion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:12.543771+00:00
-- url     : https://prove2.me/submissions/a0e571b9-8b3c-4c47-8402-e31b2f6bab35

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.Candidate
theorem _root_.solution :
    cushion < sideMargin .small := by
  norm_num [cushion, sideMargin, p]
end RH.Transport.Candidate
