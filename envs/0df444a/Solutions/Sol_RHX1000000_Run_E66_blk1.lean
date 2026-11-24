-- Prove2me | solution 1 for RHX1000000.Run.E66.blk1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T07:32:27.363255+00:00
-- url     : https://prove2.me/submissions/e1bfba25-b9cd-4d3c-be6c-a56249d4b2d7

import Definitions.Def_RHX1E6_RunE66
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

namespace RHX1000000.Run.E66
theorem c7 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 5, 8, 2 ^ 512, 256⟩ : ArbEcon.Off.OCfg) 5000 S6) S7 = true := by decide +kernel
theorem c8 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 5, 8, 2 ^ 512, 256⟩ : ArbEcon.Off.OCfg) 5000 S7) S8 = true := by decide +kernel
theorem c9 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 5, 8, 2 ^ 512, 256⟩ : ArbEcon.Off.OCfg) 5000 S8) S9 = true := by decide +kernel
theorem c10 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 5, 8, 2 ^ 512, 256⟩ : ArbEcon.Off.OCfg) 5000 S9) S10 = true := by decide +kernel
theorem c11 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 5, 8, 2 ^ 512, 256⟩ : ArbEcon.Off.OCfg) 5000 S10) S11 = true := by decide +kernel
theorem c12 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 5, 8, 2 ^ 512, 256⟩ : ArbEcon.Off.OCfg) 5000 S11) S12 = true := by decide +kernel

theorem blk1 : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 5, 8, 2 ^ 512, 256⟩ : ArbEcon.Off.OCfg) 30000 S6 = S12 := by
  have h7 := RHX.stoBeq_eq c7
  have h8 := RHX.runO_chain _ _ (a := 5000) (b := 5000) h7 (RHX.stoBeq_eq c8)
  have h9 := RHX.runO_chain _ _ (a := 10000) (b := 5000) h8 (RHX.stoBeq_eq c9)
  have h10 := RHX.runO_chain _ _ (a := 15000) (b := 5000) h9 (RHX.stoBeq_eq c10)
  have h11 := RHX.runO_chain _ _ (a := 20000) (b := 5000) h10 (RHX.stoBeq_eq c11)
  have h12 := RHX.runO_chain _ _ (a := 25000) (b := 5000) h11 (RHX.stoBeq_eq c12)
  exact h12

end RHX1000000.Run.E66
open ArbEcon.Off RHX1000000 RHX1000000.Run RHX1000000.Run.E66 in
theorem solution : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 5, 8, 2 ^ 512, 256⟩ : ArbEcon.Off.OCfg) 30000 S6 = S12 := by
  apply RHX1000000.Run.E66.blk1 <;> assumption
