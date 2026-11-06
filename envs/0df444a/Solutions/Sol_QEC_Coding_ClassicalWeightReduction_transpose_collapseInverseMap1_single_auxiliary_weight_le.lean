-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.transpose_collapseInverseMap1_single_auxiliary_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:58:15.157637+00:00
-- url     : https://prove2.me/submissions/a6cdce49-0034-41ab-afaf-742b6b64412a

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_collapseInverseMap1Basis_apply_auxiliary_of_not_rel
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
namespace QEC.Coding.ClassicalWeightReduction
theorem _root_.solution
    (a : AuxiliaryBit R) (L : Nat)
    (hDegree : Fintype.card (CheckNeighbor R a.1) ≤ L) :
    HammingWeight
        (wordLinearMapTranspose (collapseInverseMap1 (F := F) R)
          (Pi.single (Sum.inr a) 1)) ≤ L := by
  classical
  unfold collapseInverseMap1
  rw [wordLinearMapTranspose_linearMapOfBasisImages_single]
  change HammingWeight
      (fun b : Bit => collapseInverseMap1Basis (F := F) R b (Sum.inr a)) ≤ L
  calc
    HammingWeight
          (fun b : Bit => collapseInverseMap1Basis (F := F) R b (Sum.inr a)) =
        (hammingSupport
          (fun b : Bit =>
            collapseInverseMap1Basis (F := F) R b (Sum.inr a))).card := rfl
    _ ≤ (Finset.univ.filter fun b : Bit => R a.1 b).card := by
      apply Finset.card_le_card
      intro b hb
      simp only [hammingSupport, Finset.mem_filter, Finset.mem_univ,
        true_and] at hb ⊢
      by_contra hrel
      exact hb (collapseInverseMap1Basis_apply_auxiliary_of_not_rel
        (F := F) R b a hrel)
    _ = Fintype.card (CheckNeighbor R a.1) := by
      simp [CheckNeighbor, Fintype.card_subtype]
    _ ≤ L := hDegree
end QEC.Coding.ClassicalWeightReduction
