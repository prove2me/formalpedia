-- Prove2me | solution 1 for RHX1000000.Run.E09.blk2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T01:39:21.300585+00:00
-- url     : https://prove2.me/submissions/9663ea3d-4b06-4d0a-8a79-bbb916a59e20

import Definitions.Def_RHX1E6_RunE09
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

namespace RHX1000000.Run.E09
theorem c13 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨55, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S12) S13 = true := by decide +kernel
theorem c14 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨55, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S13) S14 = true := by decide +kernel
theorem c15 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨55, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S14) S15 = true := by decide +kernel
theorem c16 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨55, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S15) S16 = true := by decide +kernel
theorem c17 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨55, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S16) S17 = true := by decide +kernel
theorem c18 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨55, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 5000 S17) S18 = true := by decide +kernel

theorem blk2 : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨55, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 30000 S12 = S18 := by
  have h13 := RHX.stoBeq_eq c13
  have h14 := RHX.runO_chain _ _ (a := 5000) (b := 5000) h13 (RHX.stoBeq_eq c14)
  have h15 := RHX.runO_chain _ _ (a := 10000) (b := 5000) h14 (RHX.stoBeq_eq c15)
  have h16 := RHX.runO_chain _ _ (a := 15000) (b := 5000) h15 (RHX.stoBeq_eq c16)
  have h17 := RHX.runO_chain _ _ (a := 20000) (b := 5000) h16 (RHX.stoBeq_eq c17)
  have h18 := RHX.runO_chain _ _ (a := 25000) (b := 5000) h17 (RHX.stoBeq_eq c18)
  exact h18

end RHX1000000.Run.E09
open ArbEcon.Off RHX1000000 RHX1000000.Run RHX1000000.Run.E09 in
theorem solution : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨55, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 30000 S12 = S18 := by
  apply RHX1000000.Run.E09.blk2 <;> assumption
