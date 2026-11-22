-- Prove2me | solution 1 for TaoFivePrimes.rh67156_edge_piece_group_02_20261122
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-21T22:25:07.112188+00:00
-- url     : https://prove2.me/submissions/090a2171-a4e3-45aa-a3c2-641a8f875006

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RH67156EdgePieceTransfer
import Definitions.Def_row23_rh_supp_RH67156EdgePiece10
import Definitions.Def_row23_rh_supp_RH67156EdgePiece11
import Definitions.Def_row23_rh_supp_RH67156EdgePiece12
import Definitions.Def_row23_rh_supp_RH67156EdgePiece13
import Definitions.Def_row23_rh_supp_RH67156EdgePiece14
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
theorem solution (j : ℕ) (hlo : 10 ≤ j) (hhi : j < 15) : H11K.pieceJ RH67156Edge.withBoxes j = true := by
  apply RH67156Edge.pieceJ_of_checked j (by omega)
  interval_cases j
  · exact RH67156Edge.piece10_checked
  · exact RH67156Edge.piece11_checked
  · exact RH67156Edge.piece12_checked
  · exact RH67156Edge.piece13_checked
  · exact RH67156Edge.piece14_checked
