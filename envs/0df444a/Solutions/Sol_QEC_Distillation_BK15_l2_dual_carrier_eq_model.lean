-- Prove2me | solution 1 for QEC.Distillation.BK15.l2_dual_carrier_eq_model
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:06:35.111372+00:00
-- url     : https://prove2.me/submissions/9bf6292c-019a-42b5-8483-9c5e621eeefa

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l2DualModel_dimension
import Theorems.Thm_QEC_Distillation_BK15_L2DualModel_le_L2_dual
import Theorems.Thm_QEC_Distillation_BK15_l2_dual_dimension
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
theorem _root_.solution : L2.dual.carrier = L2DualModel.carrier := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq L2DualModel_le_L2_dual
  simpa only [Dimension_eq_finrank_carrier] using
    l2DualModel_dimension.trans l2_dual_dimension.symm
end QEC.Distillation.BK15
