-- Prove2me | solution 1 for RHX1000000.Edge.piece_13
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T02:18:10.658384+00:00
-- url     : https://prove2.me/submissions/07b8c0b6-a89d-4cd3-bf29-a6f1bcd698f4

import Definitions.Def_RHX_Edge1000000Data
import Definitions.Def_ArdaRS_Config64
import Theorems.Thm_RHX1000000_Run_E13_blk0
import Theorems.Thm_RHX1000000_Run_E13_blk1
import Theorems.Thm_RHX1000000_Run_E13_blk2
import Theorems.Thm_RHX1000000_Run_E13_blk3
import Theorems.Thm_RHX1000000_Run_E13_blk4
import Theorems.Thm_RHX1000000_Run_E13_blk5
import Theorems.Thm_RHX1000000_Run_E13_blk6
import Theorems.Thm_RHX1000000_Run_E13_blk7
import Theorems.Thm_RHX1000000_Run_E13_blk8
import Theorems.Thm_RHX1000000_Run_E13_blk9
import Theorems.Thm_RHX1000000_Run_E13_run
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

namespace RHX1000000.Edge.P13
theorem ok : Arb4.pieceOK 1000000 0 300000 RHX1000000.Edge.E.L (RHX1000000.Edge.E.pc 13) = true :=
  RHX.pieceOK_of_run _ _ _ _ _ _ RHX1000000.Run.E13.run (by decide +kernel)
theorem i1 : Arb4.inRad (RHX1000000.Edge.E.x 13) (RHX1000000.Edge.E.pc 13) = true := by decide +kernel
theorem i2 : Arb4.inRad (RHX1000000.Edge.E.x (13 + 1)) (RHX1000000.Edge.E.pc 13) = true := by decide +kernel
end RHX1000000.Edge.P13

theorem RHX1000000.Edge.piece_13 : H11K.pieceJ RHX1000000.Edge.E 13 = true := RHX.pieceJ_of _ _ RHX1000000.Edge.P13.ok RHX1000000.Edge.P13.i1 RHX1000000.Edge.P13.i2
open ArbEcon.Off in
theorem solution : H11K.pieceJ RHX1000000.Edge.E 13 = true := by
  apply RHX1000000.Edge.piece_13 <;> assumption
