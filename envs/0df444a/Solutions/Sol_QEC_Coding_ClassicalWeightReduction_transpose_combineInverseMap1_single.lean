-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.transpose_combineInverseMap1_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:57:13.567698+00:00
-- url     : https://prove2.me/submissions/5f8ddcf4-31e2-45c3-8262-1f2bf5ea7b69

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_wordLinearMapTranspose_linearMapOfBasisImages_single
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
omit [DecidableEq F]
namespace QEC.Coding.ClassicalWeightReduction
theorem _root_.solution
    (q : WeightReducedBit R) :
    wordLinearMapTranspose (combineInverseMap1 (F := F) R)
        (Pi.single q 1) =
      match q with
      | Sum.inl e => Pi.single (Sum.inl e.1.2) 1
      | Sum.inr a => Pi.single (Sum.inr a) 1 := by
  unfold combineInverseMap1
  rw [wordLinearMapTranspose_linearMapOfBasisImages_single]
  ext i
  cases q with
  | inl e =>
      cases i with
      | inl b =>
          simp only [combineInverseMap1Basis, allPrimaryBitCopies]
          by_cases heb : e.1.2 = b
          · subst b
            simp
          · have hbe : b ≠ e.1.2 := Ne.symm heb
            simp [heb, hbe]
      | inr a =>
          simp [combineInverseMap1Basis]
  | inr a =>
      cases i with
      | inl b =>
          simp [combineInverseMap1Basis, allPrimaryBitCopies]
      | inr a' =>
          simp only [combineInverseMap1Basis]
          by_cases haa : a = a'
          · subst a'
            simp
          · have haa' : a' ≠ a := Ne.symm haa
            simp [haa, haa']
end QEC.Coding.ClassicalWeightReduction
