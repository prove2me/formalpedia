-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.transpose_boundary1_productCochainFilling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:36:45.706059+00:00
-- url     : https://prove2.me/submissions/cda89361-dec4-4f1c-972d-9fea4556c242

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_transpose_boundary1_apply_inl
import Theorems.Thm_QEC_Coding_DistanceBalancing_transpose_boundary1_apply_inr
import Theorems.Thm_QEC_Coding_DistanceBalancing_projectedSourceCochain_eq
import Theorems.Thm_QEC_Coding_DistanceBalancing_transpose_sourceBoundary2_sourceCochainLift
import Theorems.Thm_QEC_Coding_DistanceBalancing_transpose_sourceBoundary1_projectedSourceCochainFilling
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
    (hFill : ∀ a : classicalBit,
      projectedSourceCochain D S x a ∈
        (sourceChainComplex D).firstCoboundaryCheckCode.carrier) :
    wordLinearMapTranspose (boundary1 D)
      (productCochainFilling D S x hFill) = x := by
  ext q
  cases q with
  | inl q =>
      rcases q with ⟨x1, a⟩
      rw [transpose_boundary1_apply_inl]
      have hSource := congrFun
        (transpose_sourceBoundary1_projectedSourceCochainFilling
          D S x hFill a) x1
      have hFirst :
          (∑ x0 : xZero,
            D.xBoundary1 x0 x1 *
              productCochainFilling D S x hFill (Sum.inl (x0, a))) =
            projectedSourceCochain D S x a x1 := by
        calc
          (∑ x0 : xZero,
              D.xBoundary1 x0 x1 *
                productCochainFilling D S x hFill (Sum.inl (x0, a))) =
              ∑ x0 : xZero,
                projectedSourceCochainFilling D S x hFill a x0 *
                  D.xBoundary1 x0 x1 := by
            apply Finset.sum_congr rfl
            intro x0 _hx0
            change D.xBoundary1 x0 x1 *
                projectedSourceCochainFilling D S x hFill a x0 =
              projectedSourceCochainFilling D S x hFill a x0 *
                D.xBoundary1 x0 x1
            exact mul_comm _ _
          _ = projectedSourceCochain D S x a x1 := by
            simpa [sourceChainComplex,
              wordLinearMapTranspose_toLin'_apply] using hSource
      rw [hFirst]
      have hProjected := congrFun (projectedSourceCochain_eq D S x a) x1
      rw [hProjected]
      simp only [productCochainFilling, sourceCochainLift,
        Sum.elim_inr, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, xOneBitSlice]
      calc
        (x (Sum.inl (x1, a)) +
            ∑ b : classicalCheck,
              D.classicalBoundary b a *
                sourceCochainContraction x (fun a => S a b) x1) +
            ∑ b : classicalCheck,
              D.classicalBoundary b a *
                sourceCochainContraction x (fun a => S a b) x1 =
          x (Sum.inl (x1, a)) +
            ((∑ b : classicalCheck,
                D.classicalBoundary b a *
                  sourceCochainContraction x (fun a => S a b) x1) +
             (∑ b : classicalCheck,
                D.classicalBoundary b a *
                  sourceCochainContraction x (fun a => S a b) x1)) := by
            ac_rfl
        _ = x (Sum.inl (x1, a)) := by
          rw [ZModModule.add_self, add_zero]
  | inr q =>
      rcases q with ⟨x2, b⟩
      rw [transpose_boundary1_apply_inr]
      have hLift := congrFun
        (transpose_sourceBoundary2_sourceCochainLift D S hS x hx b) x2
      simpa [sourceChainComplex, wordLinearMapTranspose_toLin'_apply,
        productCochainFilling, sourceCochainLift, mul_comm,
        xTwoCheckSlice] using hLift
end QEC.Coding.DistanceBalancing
