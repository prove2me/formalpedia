-- Prove2me | solution 1 for TaoFivePrimes.rh67156_edge_piece_group_03_20261122
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-21T22:26:09.725184+00:00
-- url     : https://prove2.me/submissions/0d71a0e7-4ae9-4702-95ae-1690291f9349

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RH67156EdgePieceTransfer
import Definitions.Def_row23_rh_supp_RH67156EdgePiece15
import Definitions.Def_row23_rh_supp_RH67156EdgePiece16
import Definitions.Def_row23_rh_supp_RH67156EdgePiece17
import Definitions.Def_row23_rh_supp_RH67156EdgePiece18
import Definitions.Def_row23_rh_supp_RH67156EdgePiece19
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
theorem solution (j : ℕ) (hlo : 15 ≤ j) (hhi : j < 20) : H11K.pieceJ RH67156Edge.withBoxes j = true := by
  apply RH67156Edge.pieceJ_of_checked j (by omega)
  interval_cases j
  · exact RH67156Edge.piece15_checked
  · exact RH67156Edge.piece16_checked
  · exact RH67156Edge.piece17_checked
  · exact RH67156Edge.piece18_checked
  · exact RH67156Edge.piece19_checked
