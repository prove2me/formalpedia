-- Prove2me | solution 1 for RHX1000000.Run.E67.run
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T07:48:43.181347+00:00
-- url     : https://prove2.me/submissions/ce40fa41-7d9e-41f6-bc2b-85664d653152

import Theorems.Thm_RHX1000000_Run_E67_blk0
import Theorems.Thm_RHX1000000_Run_E67_blk1
import Theorems.Thm_RHX1000000_Run_E67_blk2
import Theorems.Thm_RHX1000000_Run_E67_blk3
import Theorems.Thm_RHX1000000_Run_E67_blk4
import Theorems.Thm_RHX1000000_Run_E67_blk5
import Theorems.Thm_RHX1000000_Run_E67_blk6
import Theorems.Thm_RHX1000000_Run_E67_blk7
import Theorems.Thm_RHX1000000_Run_E67_blk8
import Theorems.Thm_RHX1000000_Run_E67_blk9
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

namespace RHX1000000.Run.E67

theorem run : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 11, 16, 2 ^ 1024, 256⟩ : ArbEcon.Off.OCfg) 299998 (StO.init (ArbEcon.OrderK.cfg64 1000000 0) 5) = S60 := by
  have g0 := blk0
  have g1 := RHX.runO_chain _ _ g0 blk1
  have g2 := RHX.runO_chain _ _ g1 blk2
  have g3 := RHX.runO_chain _ _ g2 blk3
  have g4 := RHX.runO_chain _ _ g3 blk4
  have g5 := RHX.runO_chain _ _ g4 blk5
  have g6 := RHX.runO_chain _ _ g5 blk6
  have g7 := RHX.runO_chain _ _ g6 blk7
  have g8 := RHX.runO_chain _ _ g7 blk8
  have g9 := RHX.runO_chain _ _ g8 blk9
  exact g9

end RHX1000000.Run.E67
open ArbEcon.Off RHX1000000 RHX1000000.Run RHX1000000.Run.E67 in
theorem solution : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 11, 16, 2 ^ 1024, 256⟩ : ArbEcon.Off.OCfg) 299998 (StO.init (ArbEcon.OrderK.cfg64 1000000 0) 5) = S60 := by
  apply RHX1000000.Run.E67.run <;> assumption
