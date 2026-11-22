-- Prove2me | solution 1 for TaoFivePrimes.rh67156_edge_piece_group_01_20261122
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-21T22:24:06.090208+00:00
-- url     : https://prove2.me/submissions/b2124900-1c45-4116-a159-a7663fb6d54e

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RH67156EdgePieceTransfer
import Definitions.Def_row23_rh_supp_RH67156EdgePiece05
import Definitions.Def_row23_rh_supp_RH67156EdgePiece06
import Definitions.Def_row23_rh_supp_RH67156EdgePiece07
import Definitions.Def_row23_rh_supp_RH67156EdgePiece08
import Definitions.Def_row23_rh_supp_RH67156EdgePiece09
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
theorem solution (j : ℕ) (hlo : 5 ≤ j) (hhi : j < 10) : H11K.pieceJ RH67156Edge.withBoxes j = true := by
  apply RH67156Edge.pieceJ_of_checked j (by omega)
  interval_cases j
  · exact RH67156Edge.piece05_checked
  · exact RH67156Edge.piece06_checked
  · exact RH67156Edge.piece07_checked
  · exact RH67156Edge.piece08_checked
  · exact RH67156Edge.piece09_checked
