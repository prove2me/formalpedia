-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.classicalWeightReductionInverse_transpose_map1_single_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:59:49.272703+00:00
-- url     : https://prove2.me/submissions/31b103c2-f3d9-411f-b885-26302518686c

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_transpose_combineInverseMap1_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_transpose_collapseInverseMap1_single_original
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_transpose_collapseInverseMap1_single_auxiliary_weight_le
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
namespace QEC.Coding.ClassicalWeightReduction
theorem _root_.solution
    [CharP F 2] (h : HasNoIsolatedVertices R) (L : Nat)
    (hDegree : ∀ c : Check, Fintype.card (CheckNeighbor R c) ≤ L)
    (q : WeightReducedBit R) :
    HammingWeight
        (wordLinearMapTranspose
          (classicalWeightReductionInverseChainMap (F₀ := F) R h).map1
          (Pi.single q 1)) ≤ L := by
  simp only [classicalWeightReductionInverseChainMap,
    combineInverseChainMap, collapseInverseChainMap,
    ThreeTermChainMap.comp_map1]
  rw [wordLinearMapTranspose_comp, LinearMap.comp_apply,
    transpose_combineInverseMap1_single]
  cases q with
  | inl e =>
      rw [transpose_collapseInverseMap1_single_original]
      exact (HammingWeight_single_le_one (F := F) e.1.2).trans (by
        have hpos := h.check_card_pos R e.1.1
        have hle := hDegree e.1.1
        omega)
  | inr a =>
      exact transpose_collapseInverseMap1_single_auxiliary_weight_le
        (F := F) R a L (hDegree a.1)
end QEC.Coding.ClassicalWeightReduction
