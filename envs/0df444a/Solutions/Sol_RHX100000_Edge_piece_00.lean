-- Prove2me | solution 1 for RHX100000.Edge.piece_00
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:41:14.812944+00:00
-- url     : https://prove2.me/submissions/82809fd7-665a-4ffe-a1e8-897ed7f6b0d9

import Definitions.Def_RHX_Edge100000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem RHX100000.Edge.piece_00 : H11K.pieceJ RHX100000.Edge.E 0 = true := by decide +kernel
theorem solution : H11K.pieceJ RHX100000.Edge.E 0 = true := by
  apply RHX100000.Edge.piece_00 <;> assumption
