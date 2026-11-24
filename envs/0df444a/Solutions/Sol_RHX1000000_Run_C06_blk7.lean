-- Prove2me | solution 1 for RHX1000000.Run.C06.blk7
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T09:06:02.266501+00:00
-- url     : https://prove2.me/submissions/9da00e47-463a-4ad0-b47c-4a4d99abbccf

import Definitions.Def_RHX1E6_RunC06
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

namespace RHX1000000.Run.C06
theorem c43 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨33, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 5000 S42) S43 = true := by decide +kernel
theorem c44 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨33, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 5000 S43) S44 = true := by decide +kernel
theorem c45 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨33, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 5000 S44) S45 = true := by decide +kernel
theorem c46 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨33, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 5000 S45) S46 = true := by decide +kernel
theorem c47 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨33, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 5000 S46) S47 = true := by decide +kernel
theorem c48 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨33, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 5000 S47) S48 = true := by decide +kernel

theorem blk7 : runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨33, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 30000 S42 = S48 := by
  have h43 := RHX.stoBeq_eq c43
  have h44 := RHX.runO_chain _ _ (a := 5000) (b := 5000) h43 (RHX.stoBeq_eq c44)
  have h45 := RHX.runO_chain _ _ (a := 10000) (b := 5000) h44 (RHX.stoBeq_eq c45)
  have h46 := RHX.runO_chain _ _ (a := 15000) (b := 5000) h45 (RHX.stoBeq_eq c46)
  have h47 := RHX.runO_chain _ _ (a := 20000) (b := 5000) h46 (RHX.stoBeq_eq c47)
  have h48 := RHX.runO_chain _ _ (a := 25000) (b := 5000) h47 (RHX.stoBeq_eq c48)
  exact h48

end RHX1000000.Run.C06
open ArbEcon.Off RHX1000000 RHX1000000.Run RHX1000000.Run.C06 in
theorem solution : runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨33, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 30000 S42 = S48 := by
  apply RHX1000000.Run.C06.blk7 <;> assumption
