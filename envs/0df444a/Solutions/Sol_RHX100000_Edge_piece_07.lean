-- Prove2me | solution 1 for RHX100000.Edge.piece_07
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:41:28.914807+00:00
-- url     : https://prove2.me/submissions/4f295367-cd9d-4770-bb94-ecfe616e0797

import Definitions.Def_RHX_Edge100000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem RHX100000.Edge.piece_07 : H11K.pieceJ RHX100000.Edge.E 7 = true := by decide +kernel
theorem solution : H11K.pieceJ RHX100000.Edge.E 7 = true := by
  apply RHX100000.Edge.piece_07 <;> assumption
