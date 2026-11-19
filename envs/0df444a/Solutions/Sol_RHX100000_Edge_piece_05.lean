-- Prove2me | solution 1 for RHX100000.Edge.piece_05
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:41:24.775277+00:00
-- url     : https://prove2.me/submissions/cba50f9b-9d8a-4fa3-904f-c6c711c02946

import Definitions.Def_RHX_Edge100000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem RHX100000.Edge.piece_05 : H11K.pieceJ RHX100000.Edge.E 5 = true := by decide +kernel
theorem solution : H11K.pieceJ RHX100000.Edge.E 5 = true := by
  apply RHX100000.Edge.piece_05 <;> assumption
