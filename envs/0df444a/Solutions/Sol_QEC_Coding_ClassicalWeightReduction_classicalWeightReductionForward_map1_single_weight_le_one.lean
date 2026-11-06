-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.classicalWeightReductionForward_map1_single_weight_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:56:59.863726+00:00
-- url     : https://prove2.me/submissions/11578977-75b5-46a0-8b32-a848a3de8dd9

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_HammingWeight_single_le_one
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
    (q : WeightReducedBit R) :
    HammingWeight
        ((classicalWeightReductionForwardChainMap (F₀ := F) R h).map1
          (Pi.single q 1)) ≤ 1 := by
  cases q with
  | inl e =>
      simp only [classicalWeightReductionForwardChainMap,
        combineForwardChainMap, collapseForwardChainMap,
        ThreeTermChainMap.comp_map1, LinearMap.comp_apply]
      rw [combineForwardMap1_single]
      change HammingWeight (collapseForwardMap1 (F := F) R
        (if bitPosition R e = bitRootPosition R h e.1.2 then
          Pi.single (Sum.inl e.1.2) 1 else 0)) ≤ 1
      by_cases hp : bitPosition R e = bitRootPosition R h e.1.2
      · rw [if_pos hp, collapseForwardMap1_single]
        exact HammingWeight_single_le_one (F := F) e.1.2
      · rw [if_neg hp, map_zero]
        simp
  | inr a =>
      simp only [classicalWeightReductionForwardChainMap,
        combineForwardChainMap, collapseForwardChainMap,
        ThreeTermChainMap.comp_map1, LinearMap.comp_apply]
      rw [combineForwardMap1_single]
      change HammingWeight (collapseForwardMap1 (F := F) R
        (Pi.single (Sum.inr a) 1)) ≤ 1
      rw [collapseForwardMap1_single]
      simp [collapseForwardMap1Basis]
end QEC.Coding.ClassicalWeightReduction
