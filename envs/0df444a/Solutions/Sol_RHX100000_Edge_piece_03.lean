-- Prove2me | solution 1 for RHX100000.Edge.piece_03
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:41:20.859804+00:00
-- url     : https://prove2.me/submissions/f2559a63-e1a8-4c77-b447-d91080e7d805

import Definitions.Def_RHX_Edge100000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem RHX100000.Edge.piece_03 : H11K.pieceJ RHX100000.Edge.E 3 = true := by decide +kernel
theorem solution : H11K.pieceJ RHX100000.Edge.E 3 = true := by
  apply RHX100000.Edge.piece_03 <;> assumption
