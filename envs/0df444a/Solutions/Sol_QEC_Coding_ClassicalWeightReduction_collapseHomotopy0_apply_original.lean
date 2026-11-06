-- Prove2me | solution 1 for QEC.Coding.ClassicalWeightReduction.collapseHomotopy0_apply_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:56:46.645783+00:00
-- url     : https://prove2.me/submissions/ff35f16b-a721-49f1-ba87-77f3cee29c1b

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
    (x : Word F (BitSplitCheck R)) (b : Bit) :
    collapseHomotopy0 (F := F) R x (Sum.inl b) = 0 := by
  classical
  unfold collapseHomotopy0 linearMapOfBasisImages
  change (∑ e : BitSplitCheck R,
    x e • collapseHomotopy0Basis (F := F) R e) (Sum.inl b) = 0
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro e he
  simp [collapseHomotopy0Basis, checkPathAuxiliaryPrefix]
end QEC.Coding.ClassicalWeightReduction
