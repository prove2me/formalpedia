-- Prove2me | solution 1 for TaoFivePrimes.rh66388_edge_piece_group_00_20261115
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-14T19:47:55.271906+00:00
-- url     : https://prove2.me/submissions/395f5dff-a50d-46b2-b4e1-896934ab2e20

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RH66388EdgePieceTransfer
import Definitions.Def_row23_rh_supp_RH66388EdgePiece00
import Definitions.Def_row23_rh_supp_RH66388EdgePiece01
import Definitions.Def_row23_rh_supp_RH66388EdgePiece02
import Definitions.Def_row23_rh_supp_RH66388EdgePiece03
import Definitions.Def_row23_rh_supp_RH66388EdgePiece04
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
theorem solution (j : ℕ) (hlo : 0 ≤ j) (hhi : j < 5) : H11K.pieceJ RH66388Edge.withBoxes j = true := by
  apply RH66388Edge.pieceJ_of_checked j (by omega)
  interval_cases j
  · exact RH66388Edge.piece00_checked
  · exact RH66388Edge.piece01_checked
  · exact RH66388Edge.piece02_checked
  · exact RH66388Edge.piece03_checked
  · exact RH66388Edge.piece04_checked
