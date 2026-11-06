-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.classicalWeightReductionForward_map1_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:50:29.339611+00:00
-- url     : https://prove2.me/submissions/f3713aa0-7a1f-4a2c-91cf-78c456146b06

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Theorems.Thm_QEC_Coding_HammingWeight_linearMap_le_of_basis
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_classicalWeightReductionForward_map1_single_weight_le_one
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding
open scoped BigOperators
universe u v w
open QEC.Coding.ClassicalWeightReduction
variable {F Check Bit : Type u} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [Fintype F]
namespace QEC.Coding.ClassicalWeightReduction
theorem _root_.solution
    [CharP F 2] (h : HasNoIsolatedVertices R)
    (x : Word F (WeightReducedBit R)) :
    HammingWeight
        ((classicalWeightReductionForwardChainMap (F₀ := F) R h).map1 x) ≤
      HammingWeight x := by
  simpa using HammingWeight_linearMap_le_of_basis
    (classicalWeightReductionForwardChainMap (F₀ := F) R h).map1 1
    (classicalWeightReductionForward_map1_single_weight_le_one
      (F := F) R h) x
end QEC.Coding.ClassicalWeightReduction
