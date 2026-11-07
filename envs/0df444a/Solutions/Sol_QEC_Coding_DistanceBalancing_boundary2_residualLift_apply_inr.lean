-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.boundary2_residualLift_apply_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:37:01.259212+00:00
-- url     : https://prove2.me/submissions/b2d8c202-9169-4b7c-803d-37faab9f236a

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_boundary2_apply_inr
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
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier)
    (x2 : xTwo) (b : classicalCheck) :
    boundary2 D (residualLift D S z hFill) (Sum.inr (x2, b)) =
      sliceRemainder D z hFill (Sum.inr (x2, b)) := by
  rw [boundary2_apply_inr]
  simp only [xTwoBitSlice, residualLift]
  calc
    (∑ a : classicalBit,
        D.classicalBoundary b a *
          ∑ b' : classicalCheck,
            S a b' * sliceRemainder D z hFill (Sum.inr (x2, b'))) =
        ∑ b' : classicalCheck,
          (D.classicalBoundary * S) b b' *
            sliceRemainder D z hFill (Sum.inr (x2, b')) := by
      simp [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul,
        mul_assoc, mul_comm, mul_left_comm]
      exact Finset.sum_comm
    _ = sliceRemainder D z hFill (Sum.inr (x2, b)) := by
      change D.classicalBoundary * S = 1 at hS
      rw [hS]
      rw [Fintype.sum_eq_single b]
      · simp
      · intro b' hne
        simp [Ne.symm hne]
end QEC.Coding.DistanceBalancing
