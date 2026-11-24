-- Prove2me | solution 1 for RHX1000000.Slab.cell_07
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T09:27:24.008701+00:00
-- url     : https://prove2.me/submissions/945aee28-11b4-4ac9-ad61-674279535528

import Definitions.Def_RHX_Slab1000000Data
import Definitions.Def_ArdaRS_Config64
import Theorems.Thm_RHX1000000_Run_C07_blk0
import Theorems.Thm_RHX1000000_Run_C07_blk1
import Theorems.Thm_RHX1000000_Run_C07_blk2
import Theorems.Thm_RHX1000000_Run_C07_blk3
import Theorems.Thm_RHX1000000_Run_C07_blk4
import Theorems.Thm_RHX1000000_Run_C07_blk5
import Theorems.Thm_RHX1000000_Run_C07_blk6
import Theorems.Thm_RHX1000000_Run_C07_blk7
import Theorems.Thm_RHX1000000_Run_C07_blk8
import Theorems.Thm_RHX1000000_Run_C07_blk9
import Theorems.Thm_RHX1000000_Run_C07_run
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

namespace RHX1000000.Slab.C07
end RHX1000000.Slab.C07

theorem RHX1000000.Slab.cell_07 : Arb4.cellOK RHX1000000.Slab.S 7 = true :=
  RHX.cellOK_of_run _ _ _ RHX1000000.Run.C07.run (by decide +kernel)
open ArbEcon.Off in
theorem solution : Arb4.cellOK RHX1000000.Slab.S 7 = true := by
  apply RHX1000000.Slab.cell_07 <;> assumption
