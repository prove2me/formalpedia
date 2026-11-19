-- Prove2me | solution 1 for QEC.Distillation.BK15.l2CoefficientMap_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:03:06.04723+00:00
-- url     : https://prove2.me/submissions/91dd287c-1d09-4946-8364-d1858a51efba

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
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
theorem _root_.solution (b : Sum (Fin 4) QuadraticIndex → Bit) :
    l2CoefficientMap b = ∑ g : Sum (Fin 4) QuadraticIndex, b g • l2Generator g := by
  ext i
  simp [l2CoefficientMap, Pi.smul_apply]
end QEC.Distillation.BK15
