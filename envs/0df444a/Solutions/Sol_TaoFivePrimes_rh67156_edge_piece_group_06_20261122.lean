-- Prove2me | solution 1 for TaoFivePrimes.rh67156_edge_piece_group_06_20261122
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-21T22:31:29.168736+00:00
-- url     : https://prove2.me/submissions/1b4827b8-a92e-409d-8e22-08356d60036b

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RH67156EdgePieceTransfer
import Definitions.Def_row23_rh_supp_RH67156EdgePiece30
import Definitions.Def_row23_rh_supp_RH67156EdgePiece31
import Definitions.Def_row23_rh_supp_RH67156EdgePiece32
import Definitions.Def_row23_rh_supp_RH67156EdgePiece33
import Definitions.Def_row23_rh_supp_RH67156EdgePiece34
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
theorem solution (j : ℕ) (hlo : 30 ≤ j) (hhi : j < 35) : H11K.pieceJ RH67156Edge.withBoxes j = true := by
  apply RH67156Edge.pieceJ_of_checked j (by omega)
  interval_cases j
  · exact RH67156Edge.piece30_checked
  · exact RH67156Edge.piece31_checked
  · exact RH67156Edge.piece32_checked
  · exact RH67156Edge.piece33_checked
  · exact RH67156Edge.piece34_checked
