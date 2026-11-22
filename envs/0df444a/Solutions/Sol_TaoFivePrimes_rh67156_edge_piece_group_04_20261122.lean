-- Prove2me | solution 1 for TaoFivePrimes.rh67156_edge_piece_group_04_20261122
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-21T22:27:57.205271+00:00
-- url     : https://prove2.me/submissions/04583c0c-ad4e-4a0a-8aa4-9c2035b1426f

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RH67156EdgePieceTransfer
import Definitions.Def_row23_rh_supp_RH67156EdgePiece20
import Definitions.Def_row23_rh_supp_RH67156EdgePiece21
import Definitions.Def_row23_rh_supp_RH67156EdgePiece22
import Definitions.Def_row23_rh_supp_RH67156EdgePiece23
import Definitions.Def_row23_rh_supp_RH67156EdgePiece24
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
theorem solution (j : ℕ) (hlo : 20 ≤ j) (hhi : j < 25) : H11K.pieceJ RH67156Edge.withBoxes j = true := by
  apply RH67156Edge.pieceJ_of_checked j (by omega)
  interval_cases j
  · exact RH67156Edge.piece20_checked
  · exact RH67156Edge.piece21_checked
  · exact RH67156Edge.piece22_checked
  · exact RH67156Edge.piece23_checked
  · exact RH67156Edge.piece24_checked
