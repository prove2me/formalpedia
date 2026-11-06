-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.optionalSingle_map_auxiliaryCheckIndex_apply_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:39:22.866985+00:00
-- url     : https://prove2.me/submissions/a0614173-a8b0-41c1-a5f5-552d9ede118c

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ClassicalWeightReduction
open scoped BigOperators
universe u v w
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {Check : Type v} {Bit : Type w}
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [Fintype F] [DecidableEq F] [Fintype Bit]
namespace QEC.Coding.ClassicalWeightReduction
theorem _root_.solution
    {b b' : Bit} (hb : b ≠ b')
    (o : Option (Fin (Fintype.card (BitNeighbor R b) - 1)))
    (j : Fin (Fintype.card (BitNeighbor R b') - 1)) :
    optionalSingle (F := F) (o.map (auxiliaryCheckIndex R b))
        (Sum.inr ⟨b', j⟩) = 0 := by
  cases o <;> simp [optionalSingle, auxiliaryCheckIndex, hb]
end QEC.Coding.ClassicalWeightReduction
