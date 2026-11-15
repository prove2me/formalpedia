-- Prove2me | solution 1 for TaoFivePrimes.rh66388_edge_piece_group_02_20261115
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-14T19:53:24.834142+00:00
-- url     : https://prove2.me/submissions/2014aff1-c2ad-49d7-8844-f0400528fa47

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RH66388EdgePieceTransfer
import Definitions.Def_row23_rh_supp_RH66388EdgePiece10
import Definitions.Def_row23_rh_supp_RH66388EdgePiece11
import Definitions.Def_row23_rh_supp_RH66388EdgePiece12
import Definitions.Def_row23_rh_supp_RH66388EdgePiece13
import Definitions.Def_row23_rh_supp_RH66388EdgePiece14
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
theorem solution (j : ℕ) (hlo : 10 ≤ j) (hhi : j < 15) : H11K.pieceJ RH66388Edge.withBoxes j = true := by
  apply RH66388Edge.pieceJ_of_checked j (by omega)
  interval_cases j
  · exact RH66388Edge.piece10_checked
  · exact RH66388Edge.piece11_checked
  · exact RH66388Edge.piece12_checked
  · exact RH66388Edge.piece13_checked
  · exact RH66388Edge.piece14_checked
