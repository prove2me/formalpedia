-- Prove2me | solution 1 for TaoFivePrimes.rh66388_edge_piece_group_04_20261115
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-14T19:59:26.095908+00:00
-- url     : https://prove2.me/submissions/83040969-a551-49d7-b1ce-779e67d7171a

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RH66388EdgePieceTransfer
import Definitions.Def_row23_rh_supp_RH66388EdgePiece20
import Definitions.Def_row23_rh_supp_RH66388EdgePiece21
import Definitions.Def_row23_rh_supp_RH66388EdgePiece22
import Definitions.Def_row23_rh_supp_RH66388EdgePiece23
import Definitions.Def_row23_rh_supp_RH66388EdgePiece24
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
theorem solution (j : ℕ) (hlo : 20 ≤ j) (hhi : j < 25) : H11K.pieceJ RH66388Edge.withBoxes j = true := by
  apply RH66388Edge.pieceJ_of_checked j (by omega)
  interval_cases j
  · exact RH66388Edge.piece20_checked
  · exact RH66388Edge.piece21_checked
  · exact RH66388Edge.piece22_checked
  · exact RH66388Edge.piece23_checked
  · exact RH66388Edge.piece24_checked
