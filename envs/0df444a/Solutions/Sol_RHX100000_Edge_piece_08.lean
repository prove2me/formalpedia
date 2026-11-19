-- Prove2me | solution 1 for RHX100000.Edge.piece_08
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:41:30.803486+00:00
-- url     : https://prove2.me/submissions/cb866378-4f52-4b9e-8e11-5ac321ede0cd

import Definitions.Def_RHX_Edge100000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem RHX100000.Edge.piece_08 : H11K.pieceJ RHX100000.Edge.E 8 = true := by decide +kernel
theorem solution : H11K.pieceJ RHX100000.Edge.E 8 = true := by
  apply RHX100000.Edge.piece_08 <;> assumption
