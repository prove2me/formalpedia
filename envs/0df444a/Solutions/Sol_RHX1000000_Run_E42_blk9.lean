-- Prove2me | solution 1 for RHX1000000.Run.E42.blk9
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T04:56:39.769797+00:00
-- url     : https://prove2.me/submissions/3d50e160-8966-4cec-be17-db223812fb87

import Definitions.Def_RHX1E6_RunE42
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

namespace RHX1000000.Run.E42
theorem c55 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨11, 0, 16, 2 ^ 1024, 256⟩ : ArbEcon.Off.OCfg) 5000 S54) S55 = true := by decide +kernel
theorem c56 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨11, 0, 16, 2 ^ 1024, 256⟩ : ArbEcon.Off.OCfg) 5000 S55) S56 = true := by decide +kernel
theorem c57 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨11, 0, 16, 2 ^ 1024, 256⟩ : ArbEcon.Off.OCfg) 5000 S56) S57 = true := by decide +kernel
theorem c58 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨11, 0, 16, 2 ^ 1024, 256⟩ : ArbEcon.Off.OCfg) 5000 S57) S58 = true := by decide +kernel
theorem c59 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨11, 0, 16, 2 ^ 1024, 256⟩ : ArbEcon.Off.OCfg) 5000 S58) S59 = true := by decide +kernel
theorem c60 : RHX.stoBeq (runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨11, 0, 16, 2 ^ 1024, 256⟩ : ArbEcon.Off.OCfg) 4998 S59) S60 = true := by decide +kernel

theorem blk9 : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨11, 0, 16, 2 ^ 1024, 256⟩ : ArbEcon.Off.OCfg) 29998 S54 = S60 := by
  have h55 := RHX.stoBeq_eq c55
  have h56 := RHX.runO_chain _ _ (a := 5000) (b := 5000) h55 (RHX.stoBeq_eq c56)
  have h57 := RHX.runO_chain _ _ (a := 10000) (b := 5000) h56 (RHX.stoBeq_eq c57)
  have h58 := RHX.runO_chain _ _ (a := 15000) (b := 5000) h57 (RHX.stoBeq_eq c58)
  have h59 := RHX.runO_chain _ _ (a := 20000) (b := 5000) h58 (RHX.stoBeq_eq c59)
  have h60 := RHX.runO_chain _ _ (a := 25000) (b := 4998) h59 (RHX.stoBeq_eq c60)
  exact h60

end RHX1000000.Run.E42
open ArbEcon.Off RHX1000000 RHX1000000.Run RHX1000000.Run.E42 in
theorem solution : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨11, 0, 16, 2 ^ 1024, 256⟩ : ArbEcon.Off.OCfg) 29998 S54 = S60 := by
  apply RHX1000000.Run.E42.blk9 <;> assumption
