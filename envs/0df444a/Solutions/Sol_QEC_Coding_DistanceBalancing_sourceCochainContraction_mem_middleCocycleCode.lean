-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.sourceCochainContraction_mem_middleCocycleCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:26:04.052247+00:00
-- url     : https://prove2.me/submissions/29305d4e-d57d-4125-9f74-6dff7acd7a5e

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_transpose_boundary2_apply
import Theorems.Thm_P2M_QEC_Coding_wordLinearMapTranspose_toLin__apply_6aba8976cbc7
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
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (chainComplex D).middleCocycleCode.carrier)
    (c : Word (ZMod 2) classicalBit)
    (hc : Matrix.toLin' D.classicalBoundary c = 0) :
    sourceCochainContraction x c ∈
      (sourceChainComplex D).middleCocycleCode.carrier := by
  rw [(sourceChainComplex D).mem_middleCocycleCode_iff]
  ext x2
  have hxZero := ((chainComplex D).mem_middleCocycleCode_iff x).1 hx
  change wordLinearMapTranspose (boundary2 D) x = 0 at hxZero
  have hAt : ∀ a : classicalBit,
      (∑ x1 : xOne,
          D.xBoundary2 x1 x2 * xOneBitSlice x a x1) =
        ∑ b : classicalCheck,
          D.classicalBoundary b a * xTwoCheckSlice x b x2 := by
    intro a
    have h := congrFun hxZero (x2, a)
    simp only [Pi.zero_apply] at h
    rw [transpose_boundary2_apply] at h
    have hNeg := eq_neg_of_add_eq_zero_left h
    simpa [ZModModule.neg_eq_self] using hNeg
  change wordLinearMapTranspose (Matrix.toLin' D.xBoundary2)
    (sourceCochainContraction x c) x2 = 0
  rw [wordLinearMapTranspose_toLin'_apply]
  simp only [sourceCochainContraction, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  calc
    (∑ x1 : xOne,
        (∑ a : classicalBit, c a * xOneBitSlice x a x1) *
          D.xBoundary2 x1 x2) =
        ∑ a : classicalBit, c a *
          (∑ x1 : xOne,
            D.xBoundary2 x1 x2 * xOneBitSlice x a x1) := by
      simp [Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_comm,
        mul_left_comm]
      exact Finset.sum_comm
    _ = ∑ b : classicalCheck,
        (Matrix.toLin' D.classicalBoundary c b) *
          xTwoCheckSlice x b x2 := by
      simp_rw [hAt]
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm,
        mul_left_comm]
      exact Finset.sum_comm
    _ = 0 := by rw [hc]; simp
end QEC.Coding.DistanceBalancing
