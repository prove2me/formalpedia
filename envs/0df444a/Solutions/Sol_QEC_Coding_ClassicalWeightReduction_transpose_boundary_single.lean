-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.transpose_boundary_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:44:22.750682+00:00
-- url     : https://prove2.me/submissions/78afc5c3-d245-44c8-a8a8-ace1f95aefe8

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_wordLinearMapTranspose_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_basisBoundary_apply_eq_basisCoboundary_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ClassicalWeightReduction
open scoped BigOperators
universe u v w
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {Check : Type v} {Bit : Type w}
variable [Fintype Check] [DecidableEq Check]
variable [Fintype Bit] [DecidableEq Bit]
variable (R : Check → Bit → Prop) [DecidableRel R]
omit [DecidableEq F]
namespace QEC.Coding.ClassicalWeightReduction
theorem _root_.solution (q : WeightReducedCheck R) :
    wordLinearMapTranspose (boundary (F := F) R) (Pi.single q 1) =
      basisCoboundary (F := F) R q := by
  unfold boundary
  rw [wordLinearMapTranspose_linearMapOfBasisImages_single]
  ext i
  exact basisBoundary_apply_eq_basisCoboundary_apply (F := F) R i q
end QEC.Coding.ClassicalWeightReduction
