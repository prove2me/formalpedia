-- Prove2me | solution 1 for TaoFivePrimes.rh66388_edge_piece_group_06_20261115
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-14T20:04:24.153783+00:00
-- url     : https://prove2.me/submissions/2a3ccd4c-6183-454e-93eb-aff53aa94240

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RH66388EdgePieceTransfer
import Definitions.Def_row23_rh_supp_RH66388EdgePiece30
import Definitions.Def_row23_rh_supp_RH66388EdgePiece31
import Definitions.Def_row23_rh_supp_RH66388EdgePiece32
import Definitions.Def_row23_rh_supp_RH66388EdgePiece33
import Definitions.Def_row23_rh_supp_RH66388EdgePiece34
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
theorem solution (j : ℕ) (hlo : 30 ≤ j) (hhi : j < 35) : H11K.pieceJ RH66388Edge.withBoxes j = true := by
  apply RH66388Edge.pieceJ_of_checked j (by omega)
  interval_cases j
  · exact RH66388Edge.piece30_checked
  · exact RH66388Edge.piece31_checked
  · exact RH66388Edge.piece32_checked
  · exact RH66388Edge.piece33_checked
  · exact RH66388Edge.piece34_checked
