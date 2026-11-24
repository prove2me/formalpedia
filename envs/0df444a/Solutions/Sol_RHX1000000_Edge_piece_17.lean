-- Prove2me | solution 1 for RHX1000000.Edge.piece_17
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T02:37:38.639022+00:00
-- url     : https://prove2.me/submissions/dcb92619-53a5-4683-8911-e4098e508a45

import Definitions.Def_RHX_Edge1000000Data
import Definitions.Def_ArdaRS_Config64
import Theorems.Thm_RHX1000000_Run_E17_blk0
import Theorems.Thm_RHX1000000_Run_E17_blk1
import Theorems.Thm_RHX1000000_Run_E17_blk2
import Theorems.Thm_RHX1000000_Run_E17_blk3
import Theorems.Thm_RHX1000000_Run_E17_blk4
import Theorems.Thm_RHX1000000_Run_E17_blk5
import Theorems.Thm_RHX1000000_Run_E17_blk6
import Theorems.Thm_RHX1000000_Run_E17_blk7
import Theorems.Thm_RHX1000000_Run_E17_blk8
import Theorems.Thm_RHX1000000_Run_E17_blk9
import Theorems.Thm_RHX1000000_Run_E17_run
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

namespace RHX1000000.Edge.P17
theorem ok : Arb4.pieceOK 1000000 0 300000 RHX1000000.Edge.E.L (RHX1000000.Edge.E.pc 17) = true :=
  RHX.pieceOK_of_run _ _ _ _ _ _ RHX1000000.Run.E17.run (by decide +kernel)
theorem i1 : Arb4.inRad (RHX1000000.Edge.E.x 17) (RHX1000000.Edge.E.pc 17) = true := by decide +kernel
theorem i2 : Arb4.inRad (RHX1000000.Edge.E.x (17 + 1)) (RHX1000000.Edge.E.pc 17) = true := by decide +kernel
end RHX1000000.Edge.P17

theorem RHX1000000.Edge.piece_17 : H11K.pieceJ RHX1000000.Edge.E 17 = true := RHX.pieceJ_of _ _ RHX1000000.Edge.P17.ok RHX1000000.Edge.P17.i1 RHX1000000.Edge.P17.i2
open ArbEcon.Off in
theorem solution : H11K.pieceJ RHX1000000.Edge.E 17 = true := by
  apply RHX1000000.Edge.piece_17 <;> assumption
