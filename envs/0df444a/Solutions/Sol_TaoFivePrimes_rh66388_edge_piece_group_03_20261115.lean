-- Prove2me | solution 1 for TaoFivePrimes.rh66388_edge_piece_group_03_20261115
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-14T19:56:15.114655+00:00
-- url     : https://prove2.me/submissions/3ebaf181-eff2-4230-bd46-1aa10b2f8709

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RH66388EdgePieceTransfer
import Definitions.Def_row23_rh_supp_RH66388EdgePiece15
import Definitions.Def_row23_rh_supp_RH66388EdgePiece16
import Definitions.Def_row23_rh_supp_RH66388EdgePiece17
import Definitions.Def_row23_rh_supp_RH66388EdgePiece18
import Definitions.Def_row23_rh_supp_RH66388EdgePiece19
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
theorem solution (j : ℕ) (hlo : 15 ≤ j) (hhi : j < 20) : H11K.pieceJ RH66388Edge.withBoxes j = true := by
  apply RH66388Edge.pieceJ_of_checked j (by omega)
  interval_cases j
  · exact RH66388Edge.piece15_checked
  · exact RH66388Edge.piece16_checked
  · exact RH66388Edge.piece17_checked
  · exact RH66388Edge.piece18_checked
  · exact RH66388Edge.piece19_checked
