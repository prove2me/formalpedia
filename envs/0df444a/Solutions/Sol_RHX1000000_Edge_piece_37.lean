-- Prove2me | solution 1 for RHX1000000.Edge.piece_37
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T04:40:18.784442+00:00
-- url     : https://prove2.me/submissions/63f1a047-58a5-4750-a90a-02e2e5d4222a

import Definitions.Def_RHX_Edge1000000Data
import Definitions.Def_ArdaRS_Config64
import Theorems.Thm_RHX1000000_Run_E37_blk0
import Theorems.Thm_RHX1000000_Run_E37_blk1
import Theorems.Thm_RHX1000000_Run_E37_blk2
import Theorems.Thm_RHX1000000_Run_E37_blk3
import Theorems.Thm_RHX1000000_Run_E37_blk4
import Theorems.Thm_RHX1000000_Run_E37_blk5
import Theorems.Thm_RHX1000000_Run_E37_blk6
import Theorems.Thm_RHX1000000_Run_E37_blk7
import Theorems.Thm_RHX1000000_Run_E37_blk8
import Theorems.Thm_RHX1000000_Run_E37_blk9
import Theorems.Thm_RHX1000000_Run_E37_run
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

namespace RHX1000000.Edge.P37

theorem piece37_oc :
    (RHX1000000.Edge.E.pc 37).oc =
      (⟨27, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) := by
  rfl

theorem piece37_run_for_pc :
    runO
      (ArbEcon.OrderK.cfg64 1000000 0)
      (RHX1000000.Edge.E.pc 37).oc
      (300000 - 2)
      (StO.init (ArbEcon.OrderK.cfg64 1000000 0) 5)
      = RHX1000000.Run.E37.S60 := by
  rw [piece37_oc]
  exact RHX1000000.Run.E37.run

theorem piece37_finish_check :
    RHX.pieceOKs
      1000000 0 300000
      RHX1000000.Edge.E.L
      (RHX1000000.Edge.E.pc 37)
      RHX1000000.Run.E37.S60 = true := by
  decide +kernel

theorem ok :
    Arb4.pieceOK
      1000000 0 300000
      RHX1000000.Edge.E.L
      (RHX1000000.Edge.E.pc 37) = true :=
  RHX.pieceOK_of_run
    1000000 0 300000
    RHX1000000.Edge.E.L
    (RHX1000000.Edge.E.pc 37)
    RHX1000000.Run.E37.S60
    piece37_run_for_pc
    piece37_finish_check

theorem i1 :
    Arb4.inRad
      (RHX1000000.Edge.E.x 37)
      (RHX1000000.Edge.E.pc 37) = true := by
  decide +kernel

theorem i2 :
    Arb4.inRad
      (RHX1000000.Edge.E.x (37 + 1))
      (RHX1000000.Edge.E.pc 37) = true := by
  decide +kernel

end RHX1000000.Edge.P37

theorem RHX1000000.Edge.piece_37 :
    H11K.pieceJ RHX1000000.Edge.E 37 = true :=
  RHX.pieceJ_of _ _ RHX1000000.Edge.P37.ok RHX1000000.Edge.P37.i1 RHX1000000.Edge.P37.i2
open ArbEcon.Off in
theorem solution :
    H11K.pieceJ RHX1000000.Edge.E 37 = true := by
  apply RHX1000000.Edge.piece_37 <;> assumption
