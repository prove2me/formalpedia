-- Prove2me | solution 1 for TaoFivePrimes.rh66388_edge_piece_group_08_20261115
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-14T20:08:17.121582+00:00
-- url     : https://prove2.me/submissions/022fe269-7407-4f8c-b097-018cee60ed1e

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RH66388EdgePieceTransfer
import Definitions.Def_row23_rh_supp_RH66388EdgePiece40
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
theorem solution (j : ℕ) (hlo : 40 ≤ j) (hhi : j < 41) : H11K.pieceJ RH66388Edge.withBoxes j = true := by
  apply RH66388Edge.pieceJ_of_checked j (by omega)
  interval_cases j
  · exact RH66388Edge.piece40_checked
