-- Prove2me | solution 1 for QEC.Distillation.BK15.wordPairing_l1CoefficientMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:04:55.305626+00:00
-- url     : https://prove2.me/submissions/e77b671e-16fb-45db-bf59-c7f1b8febcef

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l1CoefficientMap_eq_sum
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
theorem _root_.solution (w : Word) (a : Fin 4 → Bit) :
    wordPairing w (l1CoefficientMap a) =
      ∑ j : Fin 4, a j • wordPairing w (linearGenerator j) := by
  simp only [l1CoefficientMap_eq_sum, map_sum, map_smul]
end QEC.Distillation.BK15
