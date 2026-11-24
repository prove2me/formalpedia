-- Prove2me | solution 1 for RHX1000000.Run.E13.blk8
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T02:05:19.218077+00:00
-- url     : https://prove2.me/submissions/8eb3c67c-0350-4beb-8de5-645131d8eb32

import Definitions.Def_RHX1E6_RunE13
import Definitions.Def_RHX_Edge1000000Data
import Definitions.Def_ArdaRS_Config64
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

namespace RHX1000000.Run.E13
theorem c49 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨51, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S48) S49 = true := by decide +kernel
theorem c50 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨51, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S49) S50 = true := by decide +kernel
theorem c51 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨51, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S50) S51 = true := by decide +kernel
theorem c52 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨51, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S51) S52 = true := by decide +kernel
theorem c53 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨51, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S52) S53 = true := by decide +kernel
theorem c54 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨51, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S53) S54 = true := by decide +kernel

theorem blk8 : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨51, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 30000 S48 = S54 := by
  have h49 := RHX.stoBeq_eq c49
  have h50 := RHX.runO_chain _ _ (a := 5000) (b := 5000) h49 (RHX.stoBeq_eq c50)
  have h51 := RHX.runO_chain _ _ (a := 10000) (b := 5000) h50 (RHX.stoBeq_eq c51)
  have h52 := RHX.runO_chain _ _ (a := 15000) (b := 5000) h51 (RHX.stoBeq_eq c52)
  have h53 := RHX.runO_chain _ _ (a := 20000) (b := 5000) h52 (RHX.stoBeq_eq c53)
  have h54 := RHX.runO_chain _ _ (a := 25000) (b := 5000) h53 (RHX.stoBeq_eq c54)
  exact h54

end RHX1000000.Run.E13
open ArbEcon.Off RHX1000000 RHX1000000.Run RHX1000000.Run.E13 in
theorem solution : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨51, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 30000 S48 = S54 := by
  apply RHX1000000.Run.E13.blk8 <;> assumption
