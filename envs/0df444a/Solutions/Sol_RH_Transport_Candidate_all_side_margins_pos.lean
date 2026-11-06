-- Prove2me | solution 1 for RH.Transport.Candidate.all_side_margins_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:59:48.170309+00:00
-- url     : https://prove2.me/submissions/c97b4640-b2d8-400d-b053-9eabc99f2984

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
import Theorems.Thm_RH_Transport_Candidate_sideMargin_eq_value

set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.Candidate
theorem _root_.solution (term : SideCondition) :
    0 < sideMargin term := by
  rw [sideMargin_eq_value]
  cases term <;> norm_num [sideMarginValue]
end RH.Transport.Candidate
