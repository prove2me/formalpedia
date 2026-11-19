-- Prove2me | solution 1 for QEC.Distillation.BK15.l1_dual_carrier_eq_l1Syndrome_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:09:30.689182+00:00
-- url     : https://prove2.me/submissions/1c8d6f24-2615-4236-a324-bfaad57687d4

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_linearGenerator_mem_L1
import Theorems.Thm_QEC_Distillation_BK15_l1Syndrome_zero_pairing
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution :
    L1.dual.carrier = LinearMap.ker l1Syndrome := by
  apply le_antisymm
  · intro w hw
    change l1Syndrome w = 0
    funext j
    have hj := (L1.mem_dual w).1 hw (linearGenerator j) (linearGenerator_mem_L1 j)
    simpa [l1Syndrome] using hj
  · intro w hw
    change l1Syndrome w = 0 at hw
    refine (L1.mem_dual w).2 ?_
    rintro c ⟨a, rfl⟩
    exact l1Syndrome_zero_pairing w a hw
end QEC.Distillation.BK15
