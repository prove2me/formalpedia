-- Prove2me | solution 1 for RHX100000.Edge.piece_02
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:41:18.702842+00:00
-- url     : https://prove2.me/submissions/46e3b80d-75b5-4703-b929-dc376a15e14c

import Definitions.Def_RHX_Edge100000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem RHX100000.Edge.piece_02 : H11K.pieceJ RHX100000.Edge.E 2 = true := by decide +kernel
theorem solution : H11K.pieceJ RHX100000.Edge.E 2 = true := by
  apply RHX100000.Edge.piece_02 <;> assumption
