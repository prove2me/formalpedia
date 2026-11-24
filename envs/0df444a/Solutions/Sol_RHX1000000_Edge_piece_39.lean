-- Prove2me | solution 1 for RHX1000000.Edge.piece_39
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T04:49:59.828689+00:00
-- url     : https://prove2.me/submissions/eec7d14f-f158-48ca-b6e0-c85700a74a86

import Definitions.Def_RHX_Edge1000000Data
import Definitions.Def_ArdaRS_Config64
import Theorems.Thm_RHX1000000_Run_E39_blk0
import Theorems.Thm_RHX1000000_Run_E39_blk1
import Theorems.Thm_RHX1000000_Run_E39_blk2
import Theorems.Thm_RHX1000000_Run_E39_blk3
import Theorems.Thm_RHX1000000_Run_E39_blk4
import Theorems.Thm_RHX1000000_Run_E39_blk5
import Theorems.Thm_RHX1000000_Run_E39_blk6
import Theorems.Thm_RHX1000000_Run_E39_blk7
import Theorems.Thm_RHX1000000_Run_E39_blk8
import Theorems.Thm_RHX1000000_Run_E39_blk9
import Theorems.Thm_RHX1000000_Run_E39_run
import Theorems.Thm_RHX_accBeq_eq
import Theorems.Thm_RHX_accsBeq_eq
import Theorems.Thm_RHX_boxOK_of_run
import Theorems.Thm_RHX_cellOK_of_run
import Theorems.Thm_RHX_pieceJ_of
import Theorems.Thm_RHX_pieceOK_of
import Theorems.Thm_RHX_pieceOK_of_run
import Theorems.Thm_RHX_runO_add
import Theorems.Thm_RHX_runO_chain
import Theorems.Thm_RHX_runO_succ
import Theorems.Thm_RHX_stoBeq_eq
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open ArbEcon.Off

namespace RHX1000000.Edge.P39
theorem ok : Arb4.pieceOK 1000000 0 300000 RHX1000000.Edge.E.L (RHX1000000.Edge.E.pc 39) = true :=
  RHX.pieceOK_of_run _ _ _ _ _ _ RHX1000000.Run.E39.run (by decide +kernel)
theorem i1 : Arb4.inRad (RHX1000000.Edge.E.x 39) (RHX1000000.Edge.E.pc 39) = true := by decide +kernel
theorem i2 : Arb4.inRad (RHX1000000.Edge.E.x (39 + 1)) (RHX1000000.Edge.E.pc 39) = true := by decide +kernel
end RHX1000000.Edge.P39

theorem RHX1000000.Edge.piece_39 : H11K.pieceJ RHX1000000.Edge.E 39 = true := RHX.pieceJ_of _ _ RHX1000000.Edge.P39.ok RHX1000000.Edge.P39.i1 RHX1000000.Edge.P39.i2
open ArbEcon.Off in
theorem solution : H11K.pieceJ RHX1000000.Edge.E 39 = true := by
  apply RHX1000000.Edge.piece_39 <;> assumption
