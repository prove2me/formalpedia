-- Prove2me | solution 1 for TaoFivePrimes.rh66388_edge_piece_group_07_20261115
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-14T20:07:14.005566+00:00
-- url     : https://prove2.me/submissions/0f5b1b9c-e5be-494b-b316-bcafbe122370

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RH66388EdgePieceTransfer
import Definitions.Def_row23_rh_supp_RH66388EdgePiece35
import Definitions.Def_row23_rh_supp_RH66388EdgePiece36
import Definitions.Def_row23_rh_supp_RH66388EdgePiece37
import Definitions.Def_row23_rh_supp_RH66388EdgePiece38
import Definitions.Def_row23_rh_supp_RH66388EdgePiece39
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
theorem solution (j : ℕ) (hlo : 35 ≤ j) (hhi : j < 40) : H11K.pieceJ RH66388Edge.withBoxes j = true := by
  apply RH66388Edge.pieceJ_of_checked j (by omega)
  interval_cases j
  · exact RH66388Edge.piece35_checked
  · exact RH66388Edge.piece36_checked
  · exact RH66388Edge.piece37_checked
  · exact RH66388Edge.piece38_checked
  · exact RH66388Edge.piece39_checked
