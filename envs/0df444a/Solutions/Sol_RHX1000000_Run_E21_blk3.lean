-- Prove2me | solution 1 for RHX1000000.Run.E21.blk3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T02:47:24.436175+00:00
-- url     : https://prove2.me/submissions/bb6618ae-dd5c-40f2-939e-736c74ba065d

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
theorem c19 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨43, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S18) S19 = true := by decide +kernel
theorem c20 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨43, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S19) S20 = true := by decide +kernel
theorem c21 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨43, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S20) S21 = true := by decide +kernel
theorem c22 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨43, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S21) S22 = true := by decide +kernel
theorem c23 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨43, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S22) S23 = true := by decide +kernel
theorem c24 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨43, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S23) S24 = true := by decide +kernel

theorem blk3 : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨43, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 30000 S18 = S24 := by
  have h19 := RHX.stoBeq_eq c19
  have h20 := RHX.runO_chain _ _ (a := 5000) (b := 5000) h19 (RHX.stoBeq_eq c20)
  have h21 := RHX.runO_chain _ _ (a := 10000) (b := 5000) h20 (RHX.stoBeq_eq c21)
  have h22 := RHX.runO_chain _ _ (a := 15000) (b := 5000) h21 (RHX.stoBeq_eq c22)
  have h23 := RHX.runO_chain _ _ (a := 20000) (b := 5000) h22 (RHX.stoBeq_eq c23)
  have h24 := RHX.runO_chain _ _ (a := 25000) (b := 5000) h23 (RHX.stoBeq_eq c24)
  exact h24

end RHX1000000.Run.E21
open ArbEcon.Off RHX1000000 RHX1000000.Run RHX1000000.Run.E21 in
theorem solution : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨43, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 30000 S18 = S24 := by
  apply RHX1000000.Run.E21.blk3 <;> assumption
