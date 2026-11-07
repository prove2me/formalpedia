-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJNInFractionField_mem_Q_of_mem_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:50:28.560055+00:00
-- url     : https://prove2.me/submissions/ed980e7d-7569-4205-992c-ed009cb6b59d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_bivariateFraction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_taylor_ne_zero_of_original_denominator
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalSeries_finiteFraction_descent
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJN_mem_Q_of_finiteRationalSeriesEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFiniteClearedComplexSum_taylor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_support_sum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalBivariateFraction_taylor_equation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearingBound_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (hc : lpsOriginalJNInFractionField N hN ∈ lpsOriginalGeneratedFunctionField M hM) :
    lpsOriginalJNInFractionField N hN ∈ lpsOriginalGeneratedFunctionFieldQ M hM := by
  classical
  obtain ⟨G, H, hH, hfrac⟩ := lpsOriginalGeneratedFunctionField_bivariateFraction
    M hM (lpsOriginalJNInFractionField N hN) hc
  let holoMap := algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
  have hH' : holoMap (lpsOriginalBivariateHolomorphicEval M hM H) ≠ 0 := fun he =>
    hH (IsFractionRing.injective LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
      (he.trans (map_zero holoMap).symm))
  have he : lpsOriginalJNHolomorphic N hN *
      lpsOriginalBivariateHolomorphicEval M hM H =
      lpsOriginalBivariateHolomorphicEval M hM G := by
    apply IsFractionRing.injective LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
    change holoMap (_ * _) = holoMap _
    rw [map_mul]
    exact (eq_div_iff hH').mp hfrac
  let B := max (lpsOriginalClearingBound M G) (lpsOriginalClearingBound M H)
  have hGbound : lpsOriginalClearingBound M G ≤ B := le_max_left _ _
  have hHbound : lpsOriginalClearingBound M H ≤ B := le_max_right _ _
  let I := Sum (LPSOriginalBivariateSupport G) (LPSOriginalBivariateSupport H)
  let u : I → ℕ := Sum.elim (fun s => s.2.val) (fun s => s.2.val)
  let v : I → ℕ := Sum.elim (fun s => s.1.val) (fun s => s.1.val)
  let a : I → ℂ := Sum.elim (fun s => (G.coeff s.1.val).coeff s.2.val) (fun _ => 0)
  let b : I → ℂ := Sum.elim (fun _ => 0) (fun s => (H.coeff s.1.val).coeff s.2.val)
  have haeq : lpsOriginalFiniteClearedComplexSum M B u v a =
      lpsOriginalClearedCusp M B G := by
    unfold lpsOriginalFiniteClearedComplexSum
    change (∑ s : Sum (LPSOriginalBivariateSupport G) (LPSOriginalBivariateSupport H),
      fun q => a s * lpsOriginalClearedMonomial M B (u s) (v s) q) = _
    rw [Fintype.sum_sum_type, lpsOriginalClearedCusp_support_sum]
    simp only [a, u, v, Sum.elim_inl, Sum.elim_inr, zero_mul]
    funext q
    simp
  have hbeq : lpsOriginalFiniteClearedComplexSum M B u v b =
      lpsOriginalClearedCusp M B H := by
    unfold lpsOriginalFiniteClearedComplexSum
    change (∑ s : Sum (LPSOriginalBivariateSupport G) (LPSOriginalBivariateSupport H),
      fun q => b s * lpsOriginalClearedMonomial M B (u s) (v s) q) = _
    rw [Fintype.sum_sum_type, lpsOriginalClearedCusp_support_sum]
    simp only [b, u, v, Sum.elim_inl, Sum.elim_inr, zero_mul]
    funext q
    simp
  let T : I → PowerSeries ℚ := fun s =>
    lpsOriginalClearedFormalMonomial M (Nat.ne_of_gt hM) B (u s) (v s)
  have hrel := lpsOriginalBivariateFraction_taylor_equation N M hN hM G H B
    hGbound hHbound he
  rw [← haeq, ← hbeq,
    lpsOriginalFiniteClearedComplexSum_taylor M (Nat.ne_of_gt hM),
    lpsOriginalFiniteClearedComplexSum_taylor M (Nat.ne_of_gt hM)] at hrel
  have hden := lpsOriginalClearedCusp_taylor_ne_zero_of_original_denominator M hM B H
    hHbound hH
  rw [← hbeq, lpsOriginalFiniteClearedComplexSum_taylor M (Nat.ne_of_gt hM)] at hden
  obtain ⟨aq, bq, hab, hnonzero⟩ := lpsOriginalRationalSeries_finiteFraction_descent
    (PowerSeries.X ^ N) (PowerSeries.expand N (Nat.ne_of_gt hN) lpsOriginalJQSeries)
    T a b hrel hden
  apply lpsOriginalJN_mem_Q_of_finiteRationalSeriesEquation N M hN hM B u v aq bq
  · intro s
    cases s with
    | inl s => exact (lpsOriginalClearingBound_le M G s.1.property s.2.property).trans hGbound
    | inr s => exact (lpsOriginalClearingBound_le M H s.1.property s.2.property).trans hHbound
  · exact hab
  · exact hnonzero
end QEC.Coding.TannerLiftedProduct
