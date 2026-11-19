-- Prove2me | solution 1 for QEC.Distillation.BK15.wordPairing_l2CoefficientMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:05:14.3249+00:00
-- url     : https://prove2.me/submissions/08635a9c-5064-4aab-ba10-f5ff5541a5da

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l2CoefficientMap_eq_sum
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
theorem _root_.solution (w : Word)
    (b : Sum (Fin 4) QuadraticIndex → Bit) :
    wordPairing w (l2CoefficientMap b) =
      ∑ g : Sum (Fin 4) QuadraticIndex, b g • wordPairing w (l2Generator g) := by
  simp only [l2CoefficientMap_eq_sum, map_sum, map_smul]
end QEC.Distillation.BK15
