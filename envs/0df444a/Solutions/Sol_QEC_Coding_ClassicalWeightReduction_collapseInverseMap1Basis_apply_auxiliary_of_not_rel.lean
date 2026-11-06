-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.collapseInverseMap1Basis_apply_auxiliary_of_not_rel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:56:15.176172+00:00
-- url     : https://prove2.me/submissions/14d45937-a9dd-4384-8119-b62dc047bce9

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
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
omit [Fintype F] [DecidableEq F]
namespace QEC.Coding.ClassicalWeightReduction
theorem _root_.solution
    (b : Bit) (a : AuxiliaryBit R) (hba : ¬R a.1 b) :
    collapseInverseMap1Basis (F := F) R b (Sum.inr a) = 0 := by
  classical
  unfold collapseInverseMap1Basis
  rw [Pi.add_apply]
  have hsingle :
      (Pi.single (Sum.inl b) 1 : Word F (BitSplitBit R)) (Sum.inr a) = 0 := by
    simp
  rw [hsingle, zero_add]
  unfold collapseHomotopy0 linearMapOfBasisImages
  change (∑ e : BitSplitCheck R,
    bitSplitPrimaryBoundary (F := F) R b e •
      collapseHomotopy0Basis (F := F) R e) (Sum.inr a) = 0
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro e he
  by_cases heb : e.1.2 = b
  · have hec : e.1.1 ≠ a.1 := by
      intro hec
      apply hba
      simpa [hec, heb] using e.2
    simp [bitSplitPrimaryBoundary, heb, collapseHomotopy0Basis,
      checkPathAuxiliaryPrefix, Ne.symm hec]
  · simp [bitSplitPrimaryBoundary, heb]
end QEC.Coding.ClassicalWeightReduction
