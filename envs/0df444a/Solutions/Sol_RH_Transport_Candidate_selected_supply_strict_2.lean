-- Prove2me | solution 2 for RH.Transport.Candidate.selected_supply_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:13.099201+00:00
-- url     : https://prove2.me/submissions/0a0269de-f696-43de-872a-cf885d40e54d

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
import Theorems.Thm_RH_Transport_Candidate_all_side_margins_pos

set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.Candidate
theorem _root_.solution :
    (7 / 37 : ℝ) < ell p / (h p + zeta) := by
  have hm := all_side_margins_pos SideCondition.selectedSupply
  dsimp [sideMargin] at hm
  linarith
end RH.Transport.Candidate
