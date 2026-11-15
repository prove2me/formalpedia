-- Prove2me | solution 1 for TaoFivePrimes.rh66388_edge_piece_group_05_20261115
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-14T20:01:55.021498+00:00
-- url     : https://prove2.me/submissions/e9791baf-4747-4d36-a2a2-5dc983d99882

import Mathlib.Tactic
import Definitions.Def_row23_rh_supp_RH66388EdgePieceTransfer
import Definitions.Def_row23_rh_supp_RH66388EdgePiece25
import Definitions.Def_row23_rh_supp_RH66388EdgePiece26
import Definitions.Def_row23_rh_supp_RH66388EdgePiece27
import Definitions.Def_row23_rh_supp_RH66388EdgePiece28
import Definitions.Def_row23_rh_supp_RH66388EdgePiece29
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
theorem solution (j : ℕ) (hlo : 25 ≤ j) (hhi : j < 30) : H11K.pieceJ RH66388Edge.withBoxes j = true := by
  apply RH66388Edge.pieceJ_of_checked j (by omega)
  interval_cases j
  · exact RH66388Edge.piece25_checked
  · exact RH66388Edge.piece26_checked
  · exact RH66388Edge.piece27_checked
  · exact RH66388Edge.piece28_checked
  · exact RH66388Edge.piece29_checked
