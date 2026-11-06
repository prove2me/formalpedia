-- Prove2me | solution 1 for RH.Transport.Candidate.sideMargin_eq_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:59:16.868913+00:00
-- url     : https://prove2.me/submissions/04d4dc83-d16f-4e90-82d5-d3200b5c4ef5

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate

set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.Candidate
theorem _root_.solution (term : SideCondition) :
    sideMargin term = sideMarginValue term := by
  cases term <;>
    norm_num [sideMargin, sideMarginValue, ell, lx, ly, h, b,
      B, boundary, goodTailDecay, p, zeta]
end RH.Transport.Candidate
