-- Prove2me | solution 1 for RHX1000000.Edge.piece_14
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T02:21:25.166737+00:00
-- url     : https://prove2.me/submissions/2125528e-acb2-4b45-b86d-f6a33d1ee938

import Definitions.Def_RHX_Edge1000000Data
import Definitions.Def_ArdaRS_Config64
import Theorems.Thm_RHX1000000_Run_E14_blk0
import Theorems.Thm_RHX1000000_Run_E14_blk1
import Theorems.Thm_RHX1000000_Run_E14_blk2
import Theorems.Thm_RHX1000000_Run_E14_blk3
import Theorems.Thm_RHX1000000_Run_E14_blk4
import Theorems.Thm_RHX1000000_Run_E14_blk5
import Theorems.Thm_RHX1000000_Run_E14_blk6
import Theorems.Thm_RHX1000000_Run_E14_blk7
import Theorems.Thm_RHX1000000_Run_E14_blk8
import Theorems.Thm_RHX1000000_Run_E14_blk9
import Theorems.Thm_RHX1000000_Run_E14_run
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

namespace RHX1000000.Edge.P14
theorem ok : Arb4.pieceOK 1000000 0 300000 RHX1000000.Edge.E.L (RHX1000000.Edge.E.pc 14) = true :=
  RHX.pieceOK_of_run _ _ _ _ _ _ RHX1000000.Run.E14.run (by decide +kernel)
theorem i1 : Arb4.inRad (RHX1000000.Edge.E.x 14) (RHX1000000.Edge.E.pc 14) = true := by decide +kernel
theorem i2 : Arb4.inRad (RHX1000000.Edge.E.x (14 + 1)) (RHX1000000.Edge.E.pc 14) = true := by decide +kernel
end RHX1000000.Edge.P14

theorem RHX1000000.Edge.piece_14 : H11K.pieceJ RHX1000000.Edge.E 14 = true := RHX.pieceJ_of _ _ RHX1000000.Edge.P14.ok RHX1000000.Edge.P14.i1 RHX1000000.Edge.P14.i2
open ArbEcon.Off in
theorem solution : H11K.pieceJ RHX1000000.Edge.E 14 = true := by
  apply RHX1000000.Edge.piece_14 <;> assumption
