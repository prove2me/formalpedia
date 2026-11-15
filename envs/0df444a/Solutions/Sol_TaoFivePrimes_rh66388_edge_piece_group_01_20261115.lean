-- Prove2me | solution 1 for TaoFivePrimes.rh66388_edge_piece_group_01_20261115
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-14T19:51:37.518299+00:00
-- url     : https://prove2.me/submissions/0b67a288-fd0c-4d6a-873f-07ccddbac3f9

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RH66388EdgePieceTransfer
import Definitions.Def_row23_rh_supp_RH66388EdgePiece05
import Definitions.Def_row23_rh_supp_RH66388EdgePiece06
import Definitions.Def_row23_rh_supp_RH66388EdgePiece07
import Definitions.Def_row23_rh_supp_RH66388EdgePiece08
import Definitions.Def_row23_rh_supp_RH66388EdgePiece09
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
theorem solution (j : ℕ) (hlo : 5 ≤ j) (hhi : j < 10) : H11K.pieceJ RH66388Edge.withBoxes j = true := by
  apply RH66388Edge.pieceJ_of_checked j (by omega)
  interval_cases j
  · exact RH66388Edge.piece05_checked
  · exact RH66388Edge.piece06_checked
  · exact RH66388Edge.piece07_checked
  · exact RH66388Edge.piece08_checked
  · exact RH66388Edge.piece09_checked
