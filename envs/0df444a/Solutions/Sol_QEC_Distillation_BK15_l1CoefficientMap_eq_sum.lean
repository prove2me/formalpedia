-- Prove2me | solution 1 for QEC.Distillation.BK15.l1CoefficientMap_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:02:54.373059+00:00
-- url     : https://prove2.me/submissions/5555663b-8b19-486b-9e68-c26018e108f6

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
theorem _root_.solution (a : Fin 4 → Bit) :
    l1CoefficientMap a = ∑ j : Fin 4, a j • linearGenerator j := by
  ext i
  simp [l1CoefficientMap, Pi.smul_apply]
end QEC.Distillation.BK15
