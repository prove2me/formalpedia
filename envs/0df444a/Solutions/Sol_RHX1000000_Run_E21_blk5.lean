-- Prove2me | solution 1 for RHX1000000.Run.E21.blk5
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T02:47:28.461184+00:00
-- url     : https://prove2.me/submissions/45b81b7c-033a-4e59-bde9-c7d8d60c52fd

import Definitions.Def_RHX1E6_RunE21
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

namespace RHX1000000.Run.E21
theorem c31 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨43, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S30) S31 = true := by decide +kernel
theorem c32 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨43, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S31) S32 = true := by decide +kernel
theorem c33 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨43, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S32) S33 = true := by decide +kernel
theorem c34 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨43, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S33) S34 = true := by decide +kernel
theorem c35 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨43, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S34) S35 = true := by decide +kernel
theorem c36 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨43, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S35) S36 = true := by decide +kernel

theorem blk5 : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨43, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 30000 S30 = S36 := by
  have h31 := RHX.stoBeq_eq c31
  have h32 := RHX.runO_chain _ _ (a := 5000) (b := 5000) h31 (RHX.stoBeq_eq c32)
  have h33 := RHX.runO_chain _ _ (a := 10000) (b := 5000) h32 (RHX.stoBeq_eq c33)
  have h34 := RHX.runO_chain _ _ (a := 15000) (b := 5000) h33 (RHX.stoBeq_eq c34)
  have h35 := RHX.runO_chain _ _ (a := 20000) (b := 5000) h34 (RHX.stoBeq_eq c35)
  have h36 := RHX.runO_chain _ _ (a := 25000) (b := 5000) h35 (RHX.stoBeq_eq c36)
  exact h36

end RHX1000000.Run.E21
open ArbEcon.Off RHX1000000 RHX1000000.Run RHX1000000.Run.E21 in
theorem solution : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨43, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 30000 S30 = S36 := by
  apply RHX1000000.Run.E21.blk5 <;> assumption
