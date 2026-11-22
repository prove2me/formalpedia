-- Prove2me | solution 1 for TaoFivePrimes.rh67156_edge_piece_group_07_20261122
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-21T22:37:36.193187+00:00
-- url     : https://prove2.me/submissions/ffb17f1f-85df-4786-a104-c3bd2f021cc7

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RH67156EdgePieceTransfer
import Definitions.Def_row23_rh_supp_RH67156EdgePiece35
import Definitions.Def_row23_rh_supp_RH67156EdgePiece36
import Definitions.Def_row23_rh_supp_RH67156EdgePiece37
import Definitions.Def_row23_rh_supp_RH67156EdgePiece38
import Definitions.Def_row23_rh_supp_RH67156EdgePiece39
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
theorem solution (j : ℕ) (hlo : 35 ≤ j) (hhi : j < 40) : H11K.pieceJ RH67156Edge.withBoxes j = true := by
  apply RH67156Edge.pieceJ_of_checked j (by omega)
  interval_cases j
  · exact RH67156Edge.piece35_checked
  · exact RH67156Edge.piece36_checked
  · exact RH67156Edge.piece37_checked
  · exact RH67156Edge.piece38_checked
  · exact RH67156Edge.piece39_checked
