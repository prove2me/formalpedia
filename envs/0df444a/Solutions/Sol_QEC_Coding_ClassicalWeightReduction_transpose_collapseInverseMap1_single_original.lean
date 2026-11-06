-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.transpose_collapseInverseMap1_single_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:58:26.240193+00:00
-- url     : https://prove2.me/submissions/2f7ff8bd-d8df-42be-a2b3-f173e43403e5

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Collapse
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_collapseHomotopy0_apply_original
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
theorem _root_.solution (b : Bit) :
    wordLinearMapTranspose (collapseInverseMap1 (F := F) R)
        (Pi.single (Sum.inl b) 1) =
      Pi.single b 1 := by
  unfold collapseInverseMap1
  rw [wordLinearMapTranspose_linearMapOfBasisImages_single]
  ext b'
  simp only [collapseInverseMap1Basis, Pi.add_apply,
    collapseHomotopy0_apply_original, add_zero]
  by_cases hbb : b = b'
  · subst b'
    simp
  · have hbb' : b' ≠ b := Ne.symm hbb
    simp [hbb, hbb']
end QEC.Coding.ClassicalWeightReduction
