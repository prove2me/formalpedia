-- Prove2me | solution 1 for QEC.Distillation.BK15.l2_dual_carrier_eq_l2Syndrome_ker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:09:53.323523+00:00
-- url     : https://prove2.me/submissions/3c828454-f7ab-4458-8776-d98df053c5b8

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l2Generator_mem_L2
import Theorems.Thm_QEC_Distillation_BK15_l2Syndrome_zero_pairing
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
    L2.dual.carrier = LinearMap.ker l2Syndrome := by
  apply le_antisymm
  · intro w hw
    change l2Syndrome w = 0
    funext g
    have hg := (L2.mem_dual w).1 hw (l2Generator g) (l2Generator_mem_L2 g)
    simpa [l2Syndrome] using hg
  · intro w hw
    change l2Syndrome w = 0 at hw
    refine (L2.mem_dual w).2 ?_
    rintro c ⟨b, rfl⟩
    exact l2Syndrome_zero_pairing w b hw
end QEC.Distillation.BK15
