-- Prove2me | solution 2 for RH.Transport.Candidate.buffered_upper_scale_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:14.409678+00:00
-- url     : https://prove2.me/submissions/20b5a439-29a9-4002-b981-b130e45ca526

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
import Theorems.Thm_RH_Transport_Candidate_all_side_margins_pos

set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.Candidate
theorem _root_.solution : h p + zeta < 1 := by
  have hm := all_side_margins_pos SideCondition.bufferedUpperScale
  dsimp [sideMargin] at hm
  linarith
end RH.Transport.Candidate
