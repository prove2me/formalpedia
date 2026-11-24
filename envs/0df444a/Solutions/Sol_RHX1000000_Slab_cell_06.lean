-- Prove2me | solution 1 for RHX1000000.Slab.cell_06
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T09:24:38.252843+00:00
-- url     : https://prove2.me/submissions/55c44bcb-1c71-4a91-8bcb-a8c9f83916ac

import Definitions.Def_RHX_Slab1000000Data
import Definitions.Def_ArdaRS_Config64
import Theorems.Thm_RHX1000000_Run_C06_blk0
import Theorems.Thm_RHX1000000_Run_C06_blk1
import Theorems.Thm_RHX1000000_Run_C06_blk2
import Theorems.Thm_RHX1000000_Run_C06_blk3
import Theorems.Thm_RHX1000000_Run_C06_blk4
import Theorems.Thm_RHX1000000_Run_C06_blk5
import Theorems.Thm_RHX1000000_Run_C06_blk6
import Theorems.Thm_RHX1000000_Run_C06_blk7
import Theorems.Thm_RHX1000000_Run_C06_blk8
import Theorems.Thm_RHX1000000_Run_C06_blk9
import Theorems.Thm_RHX1000000_Run_C06_run
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

namespace RHX1000000.Slab.C06
end RHX1000000.Slab.C06

theorem RHX1000000.Slab.cell_06 : Arb4.cellOK RHX1000000.Slab.S 6 = true :=
  RHX.cellOK_of_run _ _ _ RHX1000000.Run.C06.run (by decide +kernel)
open ArbEcon.Off in
theorem solution : Arb4.cellOK RHX1000000.Slab.S 6 = true := by
  apply RHX1000000.Slab.cell_06 <;> assumption
