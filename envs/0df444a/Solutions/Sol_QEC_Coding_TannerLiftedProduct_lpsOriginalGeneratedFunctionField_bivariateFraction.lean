-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_bivariateFraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:31:40.97745+00:00
-- url     : https://prove2.me/submissions/261e90b2-5aa5-427d-a776-fcbe6346d8e5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbedding_polynomial
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
    (M : ℕ) (hM : 0 < M) (x : LPSOriginalHolomorphicFractionField)
    (hx : x ∈ lpsOriginalGeneratedFunctionField M hM) :
    ∃ G H : Polynomial (Polynomial ℂ),
      lpsOriginalBivariateHolomorphicEval M hM H ≠ 0 ∧
      x = algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
          (lpsOriginalBivariateHolomorphicEval M hM G) /
        algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
          (lpsOriginalBivariateHolomorphicEval M hM H) := by
  classical
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let e := lpsOriginalBivariateHolomorphicEval M hM
  let ι := algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
  have hC (P : Polynomial ℂ) : e (Polynomial.C P) = lpsOriginalJHolomorphicEval P := by
    simp only [e, lpsOriginalBivariateHolomorphicEval, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C]
    rfl
  have hX : e Polynomial.X = lpsOriginalJNHolomorphic M hM := by
    simp only [e, lpsOriginalBivariateHolomorphicEval, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
  have hι := IsFractionRing.injective LPSOriginalHolomorphicRing
    LPSOriginalHolomorphicFractionField
  change x ∈ IntermediateField.adjoin (FractionRing (Polynomial ℂ))
    {lpsOriginalJNInFractionField M hM} at hx
  change ∃ G H : Polynomial (Polynomial ℂ), e H ≠ 0 ∧ x = ι (e G) / ι (e H)
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
      have he : x = lpsOriginalJNInFractionField M hM := Set.mem_singleton_iff.mp hx
      subst x
      refine ⟨Polynomial.X, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
      simp only [hX, map_one, div_one]
      rfl
  | algebraMap a =>
      obtain ⟨A, B, hB, hAB⟩ := IsFractionRing.div_surjective (Polynomial ℂ) a
      refine ⟨Polynomial.C A, Polynomial.C B, ?_, ?_⟩
      · rw [hC]
        exact fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hB)
          (lpsOriginalJHolomorphicEval_injective (h.trans (map_zero _).symm))
      · change lpsOriginalJFractionEmbedding a = ι (e (Polynomial.C A)) / ι (e (Polynomial.C B))
        rw [hC, hC, ← hAB, map_div₀,
          lpsOriginalJFractionEmbedding_polynomial,
          lpsOriginalJFractionEmbedding_polynomial]
  | add x y hx hy ihx ihy =>
      obtain ⟨G, H, hH, rfl⟩ := ihx
      obtain ⟨A, B, hB, rfl⟩ := ihy
      refine ⟨G * B + A * H, H * B, ?_, ?_⟩
      · simpa only [map_mul] using mul_ne_zero hH hB
      · simp only [map_add, map_mul]
        have hH' : ι (e H) ≠ 0 := fun h => hH (hι (h.trans (map_zero ι).symm))
        have hB' : ι (e B) ≠ 0 := fun h => hB (hι (h.trans (map_zero ι).symm))
        change ι (e G) / ι (e H) + ι (e A) / ι (e B) =
          (ι (e G) * ι (e B) + ι (e A) * ι (e H)) / (ι (e H) * ι (e B))
        rw [div_add_div _ _ hH' hB', mul_comm (ι (e H)) (ι (e A))]
  | inv x hx ih =>
      obtain ⟨G, H, hH, rfl⟩ := ih
      by_cases hG : e G = 0
      · refine ⟨0, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
        simp only [hG, map_zero, zero_div, inv_zero]
      · refine ⟨H, G, hG, ?_⟩
        exact inv_div _ _
  | mul x y hx hy ihx ihy =>
      obtain ⟨G, H, hH, rfl⟩ := ihx
      obtain ⟨A, B, hB, rfl⟩ := ihy
      refine ⟨G * A, H * B, ?_, ?_⟩
      · simpa only [map_mul] using mul_ne_zero hH hB
      · simp only [map_mul]
        exact div_mul_div_comm _ _ _ _
end QEC.Coding.TannerLiftedProduct
