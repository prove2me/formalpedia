-- Prove2me | solution 1 for QEC.Distillation.BK15.l2_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:00:13.062496+00:00
-- url     : https://prove2.me/submissions/b4c99d6f-76e8-418b-a14d-f9896558a444

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_quadraticIndex_card
import Theorems.Thm_QEC_Distillation_BK15_l2CoefficientMap_injective
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
theorem _root_.solution : Dimension L2 = 10 := by
  rw [Dimension_eq_finrank_carrier]
  change Module.finrank Bit (LinearMap.range l2CoefficientMap) = 10
  rw [LinearMap.finrank_range_of_inj l2CoefficientMap_injective,
    Module.finrank_pi]
  simp [quadraticIndex_card]
end QEC.Distillation.BK15
