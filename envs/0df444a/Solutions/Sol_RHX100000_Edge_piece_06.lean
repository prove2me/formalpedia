-- Prove2me | solution 1 for RHX100000.Edge.piece_06
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:41:27.150206+00:00
-- url     : https://prove2.me/submissions/47a54ff2-b010-41c3-91e5-61186cd1fd89

import Definitions.Def_RHX_Edge100000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem RHX100000.Edge.piece_06 : H11K.pieceJ RHX100000.Edge.E 6 = true := by decide +kernel
theorem solution : H11K.pieceJ RHX100000.Edge.E 6 = true := by
  apply RHX100000.Edge.piece_06 <;> assumption
