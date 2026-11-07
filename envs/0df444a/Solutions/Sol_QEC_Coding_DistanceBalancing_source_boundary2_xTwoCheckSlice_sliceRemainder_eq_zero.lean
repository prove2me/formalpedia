-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.source_boundary2_xTwoCheckSlice_sliceRemainder_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:42:42.07121+00:00
-- url     : https://prove2.me/submissions/a262b656-654a-4e40-8da7-ba3b25c73d86

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_boundary1_apply_inr
import Theorems.Thm_QEC_Coding_DistanceBalancing_sliceRemainder_apply_inl
import Theorems.Thm_QEC_Coding_DistanceBalancing_sliceRemainder_mem_middleCycleCode
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open scoped BigOperators
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)
namespace QEC.Coding.DistanceBalancing
theorem _root_.solution
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier)
    (b : classicalCheck) :
    (sourceChainComplex D).boundary2
      (xTwoCheckSlice (sliceRemainder D z hFill) b) = 0 := by
  have hCycle := sliceRemainder_mem_middleCycleCode D z hz hFill
  have hZero := ((chainComplex D).mem_middleCycleCode_iff _).1 hCycle
  change boundary1 D (sliceRemainder D z hFill) = 0 at hZero
  ext x1
  have hAt := congrFun hZero (Sum.inr (x1, b))
  simp only [Pi.zero_apply] at hAt
  rw [boundary1_apply_inr] at hAt
  have hFirst :
      (∑ a : classicalBit,
        D.classicalBoundary b a *
          xOneBitSlice (sliceRemainder D z hFill) a x1) = 0 := by
    apply Finset.sum_eq_zero
    intro a _ha
    simp [xOneBitSlice, sliceRemainder_apply_inl]
  rw [hFirst, zero_add] at hAt
  simpa [sourceChainComplex, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, xTwoCheckSlice] using hAt
end QEC.Coding.DistanceBalancing
