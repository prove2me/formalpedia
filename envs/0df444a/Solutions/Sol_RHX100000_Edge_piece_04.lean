-- Prove2me | solution 1 for RHX100000.Edge.piece_04
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-18T22:41:22.7382+00:00
-- url     : https://prove2.me/submissions/bd5d14c7-2211-4de8-a3fa-86ee86a85fbd

import Definitions.Def_RHX_Edge100000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem RHX100000.Edge.piece_04 : H11K.pieceJ RHX100000.Edge.E 4 = true := by decide +kernel
theorem solution : H11K.pieceJ RHX100000.Edge.E 4 = true := by
  apply RHX100000.Edge.piece_04 <;> assumption
