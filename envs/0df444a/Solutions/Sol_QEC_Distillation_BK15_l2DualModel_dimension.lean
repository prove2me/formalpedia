-- Prove2me | solution 1 for QEC.Distillation.BK15.l2DualModel_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:00:20.329202+00:00
-- url     : https://prove2.me/submissions/ab6878d4-0744-40dd-bb33-52aeb9f50244

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l2DualCoefficientMap_injective
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
theorem _root_.solution : Dimension L2DualModel = 5 := by
  rw [Dimension_eq_finrank_carrier]
  change Module.finrank Bit (LinearMap.range l2DualCoefficientMap) = 5
  rw [LinearMap.finrank_range_of_inj l2DualCoefficientMap_injective,
    Module.finrank_prod, Module.finrank_pi]
  simp
end QEC.Distillation.BK15
