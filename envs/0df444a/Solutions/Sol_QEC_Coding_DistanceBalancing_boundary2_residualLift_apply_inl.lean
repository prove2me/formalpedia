-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.boundary2_residualLift_apply_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:45:53.732422+00:00
-- url     : https://prove2.me/submissions/dabcdc1f-15b9-45fb-bcb1-b0cc6acc7809

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_boundary2_apply_inl
import Theorems.Thm_QEC_Coding_DistanceBalancing_source_boundary2_xTwoCheckSlice_sliceRemainder_eq_zero
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
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier)
    (x1 : xOne) (a : classicalBit) :
    boundary2 D (residualLift D S z hFill) (Sum.inl (x1, a)) = 0 := by
  rw [boundary2_apply_inl]
  simp only [xTwoBitSlice, residualLift]
  calc
    (∑ x2 : xTwo,
        D.xBoundary2 x1 x2 *
          ∑ b : classicalCheck,
            S a b * sliceRemainder D z hFill (Sum.inr (x2, b))) =
        ∑ b : classicalCheck,
          S a b *
            (sourceChainComplex D).boundary2
              (xTwoCheckSlice (sliceRemainder D z hFill) b) x1 := by
      simp [sourceChainComplex, Matrix.toLin'_apply, Matrix.mulVec,
        dotProduct, xTwoCheckSlice, Finset.mul_sum, Finset.sum_mul,
        mul_assoc, mul_comm, mul_left_comm]
      exact Finset.sum_comm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro b _hb
      rw [congrFun
        (source_boundary2_xTwoCheckSlice_sliceRemainder_eq_zero
          D z hz hFill b) x1]
      simp
end QEC.Coding.DistanceBalancing
