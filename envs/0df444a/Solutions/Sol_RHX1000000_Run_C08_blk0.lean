-- Prove2me | solution 1 for RHX1000000.Run.C08.blk0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T09:18:16.866875+00:00
-- url     : https://prove2.me/submissions/b4a4a757-0539-4906-8a44-439d8f692915

import Definitions.Def_RHX1E6_RunC08
import Definitions.Def_RHX_Slab1000000Data
import Definitions.Def_ArdaRS_Config64
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

namespace RHX1000000.Run.C08
theorem c1 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨37, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 5000 (StO.init (ArbEcon.OrderK.cfg64 16384000025 14) 5)) S1 = true := by decide +kernel
theorem c2 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨37, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 5000 S1) S2 = true := by decide +kernel
theorem c3 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨37, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 5000 S2) S3 = true := by decide +kernel
theorem c4 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨37, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 5000 S3) S4 = true := by decide +kernel
theorem c5 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨37, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 5000 S4) S5 = true := by decide +kernel
theorem c6 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨37, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 5000 S5) S6 = true := by decide +kernel

theorem blk0 : runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨37, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 30000 (StO.init (ArbEcon.OrderK.cfg64 16384000025 14) 5) = S6 := by
  have h1 := RHX.stoBeq_eq c1
  have h2 := RHX.runO_chain _ _ (a := 5000) (b := 5000) h1 (RHX.stoBeq_eq c2)
  have h3 := RHX.runO_chain _ _ (a := 10000) (b := 5000) h2 (RHX.stoBeq_eq c3)
  have h4 := RHX.runO_chain _ _ (a := 15000) (b := 5000) h3 (RHX.stoBeq_eq c4)
  have h5 := RHX.runO_chain _ _ (a := 20000) (b := 5000) h4 (RHX.stoBeq_eq c5)
  have h6 := RHX.runO_chain _ _ (a := 25000) (b := 5000) h5 (RHX.stoBeq_eq c6)
  exact h6

end RHX1000000.Run.C08
open ArbEcon.Off RHX1000000 RHX1000000.Run RHX1000000.Run.C08 in
theorem solution : runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨37, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 30000 (StO.init (ArbEcon.OrderK.cfg64 16384000025 14) 5) = S6 := by
  apply RHX1000000.Run.C08.blk0 <;> assumption
