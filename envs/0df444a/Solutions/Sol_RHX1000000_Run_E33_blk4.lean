-- Prove2me | solution 1 for RHX1000000.Run.E33.blk4
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T03:55:42.086377+00:00
-- url     : https://prove2.me/submissions/b3eb4ab3-496a-4510-8fb1-6bdd7e59f73c

import Definitions.Def_RHX1E6_RunE33
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

namespace RHX1000000.Run.E33
theorem c25 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨31, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S24) S25 = true := by decide +kernel
theorem c26 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨31, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S25) S26 = true := by decide +kernel
theorem c27 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨31, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S26) S27 = true := by decide +kernel
theorem c28 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨31, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S27) S28 = true := by decide +kernel
theorem c29 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨31, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S28) S29 = true := by decide +kernel
theorem c30 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨31, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S29) S30 = true := by decide +kernel

theorem blk4 : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨31, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 30000 S24 = S30 := by
  have h25 := RHX.stoBeq_eq c25
  have h26 := RHX.runO_chain _ _ (a := 5000) (b := 5000) h25 (RHX.stoBeq_eq c26)
  have h27 := RHX.runO_chain _ _ (a := 10000) (b := 5000) h26 (RHX.stoBeq_eq c27)
  have h28 := RHX.runO_chain _ _ (a := 15000) (b := 5000) h27 (RHX.stoBeq_eq c28)
  have h29 := RHX.runO_chain _ _ (a := 20000) (b := 5000) h28 (RHX.stoBeq_eq c29)
  have h30 := RHX.runO_chain _ _ (a := 25000) (b := 5000) h29 (RHX.stoBeq_eq c30)
  exact h30

end RHX1000000.Run.E33
open ArbEcon.Off RHX1000000 RHX1000000.Run RHX1000000.Run.E33 in
theorem solution : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨31, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 30000 S24 = S30 := by
  apply RHX1000000.Run.E33.blk4 <;> assumption
