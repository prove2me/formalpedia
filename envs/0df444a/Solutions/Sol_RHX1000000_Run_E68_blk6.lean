-- Prove2me | solution 1 for RHX1000000.Run.E68.blk6
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T07:45:36.490821+00:00
-- url     : https://prove2.me/submissions/9bfe3066-8c15-4f00-b85a-fc4b87960d9c

import Definitions.Def_RHX1E6_RunE68
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

namespace RHX1000000.Run.E68
theorem c37 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 3, 4, 2 ^ 256, 256⟩ : ArbEcon.Off.OCfg) 5000 S36) S37 = true := by decide +kernel
theorem c38 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 3, 4, 2 ^ 256, 256⟩ : ArbEcon.Off.OCfg) 5000 S37) S38 = true := by decide +kernel
theorem c39 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 3, 4, 2 ^ 256, 256⟩ : ArbEcon.Off.OCfg) 5000 S38) S39 = true := by decide +kernel
theorem c40 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 3, 4, 2 ^ 256, 256⟩ : ArbEcon.Off.OCfg) 5000 S39) S40 = true := by decide +kernel
theorem c41 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 3, 4, 2 ^ 256, 256⟩ : ArbEcon.Off.OCfg) 5000 S40) S41 = true := by decide +kernel
theorem c42 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 3, 4, 2 ^ 256, 256⟩ : ArbEcon.Off.OCfg) 5000 S41) S42 = true := by decide +kernel

theorem blk6 : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 3, 4, 2 ^ 256, 256⟩ : ArbEcon.Off.OCfg) 30000 S36 = S42 := by
  have h37 := RHX.stoBeq_eq c37
  have h38 := RHX.runO_chain _ _ (a := 5000) (b := 5000) h37 (RHX.stoBeq_eq c38)
  have h39 := RHX.runO_chain _ _ (a := 10000) (b := 5000) h38 (RHX.stoBeq_eq c39)
  have h40 := RHX.runO_chain _ _ (a := 15000) (b := 5000) h39 (RHX.stoBeq_eq c40)
  have h41 := RHX.runO_chain _ _ (a := 20000) (b := 5000) h40 (RHX.stoBeq_eq c41)
  have h42 := RHX.runO_chain _ _ (a := 25000) (b := 5000) h41 (RHX.stoBeq_eq c42)
  exact h42

end RHX1000000.Run.E68
open ArbEcon.Off RHX1000000 RHX1000000.Run RHX1000000.Run.E68 in
theorem solution : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 3, 4, 2 ^ 256, 256⟩ : ArbEcon.Off.OCfg) 30000 S36 = S42 := by
  apply RHX1000000.Run.E68.blk6 <;> assumption
