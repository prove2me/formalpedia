-- Prove2me | solution 1 for TaoFivePrimes.rh67156_edge_piece_group_05_20261122
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-21T22:28:59.912419+00:00
-- url     : https://prove2.me/submissions/c5033de5-31c8-4811-9582-a0d6bf7e8b0f

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RH67156EdgePieceTransfer
import Definitions.Def_row23_rh_supp_RH67156EdgePiece25
import Definitions.Def_row23_rh_supp_RH67156EdgePiece26
import Definitions.Def_row23_rh_supp_RH67156EdgePiece27
import Definitions.Def_row23_rh_supp_RH67156EdgePiece28
import Definitions.Def_row23_rh_supp_RH67156EdgePiece29
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
theorem solution (j : ℕ) (hlo : 25 ≤ j) (hhi : j < 30) : H11K.pieceJ RH67156Edge.withBoxes j = true := by
  apply RH67156Edge.pieceJ_of_checked j (by omega)
  interval_cases j
  · exact RH67156Edge.piece25_checked
  · exact RH67156Edge.piece26_checked
  · exact RH67156Edge.piece27_checked
  · exact RH67156Edge.piece28_checked
  · exact RH67156Edge.piece29_checked
