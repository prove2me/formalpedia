-- Prove2me | solution 1 for RHX1000000.Edge.piece_42
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T05:06:05.871359+00:00
-- url     : https://prove2.me/submissions/521c349e-6889-4273-820a-31efb2b5e441

import Definitions.Def_RHX_Edge1000000Data
import Definitions.Def_ArdaRS_Config64
import Theorems.Thm_RHX1000000_Run_E42_blk0
import Theorems.Thm_RHX1000000_Run_E42_blk1
import Theorems.Thm_RHX1000000_Run_E42_blk2
import Theorems.Thm_RHX1000000_Run_E42_blk3
import Theorems.Thm_RHX1000000_Run_E42_blk4
import Theorems.Thm_RHX1000000_Run_E42_blk5
import Theorems.Thm_RHX1000000_Run_E42_blk6
import Theorems.Thm_RHX1000000_Run_E42_blk7
import Theorems.Thm_RHX1000000_Run_E42_blk8
import Theorems.Thm_RHX1000000_Run_E42_blk9
import Theorems.Thm_RHX1000000_Run_E42_run
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

namespace RHX1000000.Edge.P42
theorem ok : Arb4.pieceOK 1000000 0 300000 RHX1000000.Edge.E.L (RHX1000000.Edge.E.pc 42) = true :=
  RHX.pieceOK_of_run _ _ _ _ _ _ RHX1000000.Run.E42.run (by decide +kernel)
theorem i1 : Arb4.inRad (RHX1000000.Edge.E.x 42) (RHX1000000.Edge.E.pc 42) = true := by decide +kernel
theorem i2 : Arb4.inRad (RHX1000000.Edge.E.x (42 + 1)) (RHX1000000.Edge.E.pc 42) = true := by decide +kernel
end RHX1000000.Edge.P42

theorem RHX1000000.Edge.piece_42 : H11K.pieceJ RHX1000000.Edge.E 42 = true := RHX.pieceJ_of _ _ RHX1000000.Edge.P42.ok RHX1000000.Edge.P42.i1 RHX1000000.Edge.P42.i2
open ArbEcon.Off in
theorem solution : H11K.pieceJ RHX1000000.Edge.E 42 = true := by
  apply RHX1000000.Edge.piece_42 <;> assumption
