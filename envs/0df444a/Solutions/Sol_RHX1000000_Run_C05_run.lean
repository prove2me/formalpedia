-- Prove2me | solution 1 for RHX1000000.Run.C05.run
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T09:02:33.754817+00:00
-- url     : https://prove2.me/submissions/baeb5938-04ac-422e-8f31-344c9275459d

import Theorems.Thm_RHX1000000_Run_C05_blk0
import Theorems.Thm_RHX1000000_Run_C05_blk1
import Theorems.Thm_RHX1000000_Run_C05_blk2
import Theorems.Thm_RHX1000000_Run_C05_blk3
import Theorems.Thm_RHX1000000_Run_C05_blk4
import Theorems.Thm_RHX1000000_Run_C05_blk5
import Theorems.Thm_RHX1000000_Run_C05_blk6
import Theorems.Thm_RHX1000000_Run_C05_blk7
import Theorems.Thm_RHX1000000_Run_C05_blk8
import Theorems.Thm_RHX1000000_Run_C05_blk9
import Theorems.Thm_RHX_accBeq_eq
import Theorems.Thm_RHX_accsBeq_eq
import Theorems.Thm_RHX_boxOK_of_run
import Theorems.Thm_RHX_cellOK_of_run
import Theorems.Thm_RHX_pieceOK_of_run
import Theorems.Thm_RHX_runO_add
import Theorems.Thm_RHX_runO_chain
import Theorems.Thm_RHX_runO_succ
import Theorems.Thm_RHX_stoBeq_eq
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open ArbEcon.Off

namespace RHX1000000.Run.C05

theorem run : runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨31, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 299999 (StO.init (ArbEcon.OrderK.cfg64 16384000025 14) 5) = S60 := by
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

end RHX1000000.Run.C05
open ArbEcon.Off RHX1000000 RHX1000000.Run RHX1000000.Run.C05 in
theorem solution : runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨31, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 299999 (StO.init (ArbEcon.OrderK.cfg64 16384000025 14) 5) = S60 := by
  apply RHX1000000.Run.C05.run <;> assumption
