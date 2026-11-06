-- Prove2me | solution 2 for RH.Transport.Candidate.extension_supply_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:13.740492+00:00
-- url     : https://prove2.me/submissions/990ac5c8-ba05-42e3-a6a5-51e151d370c2

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_Candidate
import Theorems.Thm_RH_Transport_Candidate_all_side_margins_pos

set_option autoImplicit false
open RH RH.Transport RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section
namespace RH.Transport.Candidate
theorem _root_.solution : zeta < 5 * ell p - h p := by
  have hm := all_side_margins_pos SideCondition.strongSupply
  dsimp [sideMargin] at hm
  linarith
end RH.Transport.Candidate
