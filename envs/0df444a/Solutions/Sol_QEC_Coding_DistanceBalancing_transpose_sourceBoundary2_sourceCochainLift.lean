-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.transpose_sourceBoundary2_sourceCochainLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:27:34.944229+00:00
-- url     : https://prove2.me/submissions/a1fc647d-e151-4296-b6c9-3cb8a1cc947c

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
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hx : x ∈ (chainComplex D).middleCocycleCode.carrier)
    (b : classicalCheck) :
    wordLinearMapTranspose (sourceChainComplex D).boundary2
      (sourceCochainLift S x b) = xTwoCheckSlice x b := by
  ext x2
  have hxZero := ((chainComplex D).mem_middleCocycleCode_iff x).1 hx
  change wordLinearMapTranspose (boundary2 D) x = 0 at hxZero
  have hAt : ∀ a : classicalBit,
      (∑ x1 : xOne,
          D.xBoundary2 x1 x2 * xOneBitSlice x a x1) =
        ∑ b' : classicalCheck,
          D.classicalBoundary b' a * xTwoCheckSlice x b' x2 := by
    intro a
    have h := congrFun hxZero (x2, a)
    simp only [Pi.zero_apply] at h
    rw [transpose_boundary2_apply] at h
    have hNeg := eq_neg_of_add_eq_zero_left h
    simpa [ZModModule.neg_eq_self] using hNeg
  change wordLinearMapTranspose (Matrix.toLin' D.xBoundary2)
    (sourceCochainLift S x b) x2 = xTwoCheckSlice x b x2
  rw [wordLinearMapTranspose_toLin'_apply]
  simp only [sourceCochainLift, sourceCochainContraction,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ x1 : xOne,
        (∑ a : classicalBit, S a b * xOneBitSlice x a x1) *
          D.xBoundary2 x1 x2) =
        ∑ a : classicalBit, S a b *
          (∑ x1 : xOne,
            D.xBoundary2 x1 x2 * xOneBitSlice x a x1) := by
      simp [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm,
        mul_left_comm]
      exact Finset.sum_comm
    _ = ∑ b' : classicalCheck,
        (D.classicalBoundary * S) b' b * xTwoCheckSlice x b' x2 := by
      simp_rw [hAt]
      simp [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul,
        mul_assoc, mul_comm, mul_left_comm]
      exact Finset.sum_comm
    _ = xTwoCheckSlice x b x2 := by
      change D.classicalBoundary * S = 1 at hS
      rw [hS, Fintype.sum_eq_single b]
      · simp
      · intro b' hne
        rw [Matrix.one_apply]
        simp [hne]
end QEC.Coding.DistanceBalancing
