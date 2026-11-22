-- Prove2me | solution 1 for TaoFivePrimes.rh67156_edge_piece_group_00_20261122
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-21T22:19:31.625732+00:00
-- url     : https://prove2.me/submissions/9c03ae7a-0fd7-4e03-bba6-d00dcf7e0f25

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RH67156EdgePieceTransfer
import Definitions.Def_row23_rh_supp_RH67156EdgePiece00
import Definitions.Def_row23_rh_supp_RH67156EdgePiece01
import Definitions.Def_row23_rh_supp_RH67156EdgePiece02
import Definitions.Def_row23_rh_supp_RH67156EdgePiece03
import Definitions.Def_row23_rh_supp_RH67156EdgePiece04
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
theorem solution (j : ℕ) (hlo : 0 ≤ j) (hhi : j < 5) : H11K.pieceJ RH67156Edge.withBoxes j = true := by
  apply RH67156Edge.pieceJ_of_checked j (by omega)
  interval_cases j
  · exact RH67156Edge.piece00_checked
  · exact RH67156Edge.piece01_checked
  · exact RH67156Edge.piece02_checked
  · exact RH67156Edge.piece03_checked
  · exact RH67156Edge.piece04_checked
