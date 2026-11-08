-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalPolynomial_field_embedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:34:35.720278+00:00
-- url     : https://prove2.me/submissions/68f00d30-6d55-4e5f-ab8a-8cf79eebfcb5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNumerator
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPowerPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalFieldIntegral
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalTransferDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => LPSOriginalHolomorphicRing
local notation "H" => LPSOriginalHolomorphicFractionField
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalTransferDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalTransferDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalTransferDictionary004
omit [NeZero N]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    (lpsOriginalGeneratedFunctionField N hpos).val.toRingHom.comp
      (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos) =
    Polynomial.eval₂RingHom ((algebraMap R H).comp (algebraMap ℂ R))
      (algebraMap R H lpsOriginalJHolomorphic)⁻¹ := by
  let ψ : K →+* H := (lpsOriginalGeneratedFunctionField N hpos).val.toRingHom
  let γ : ℂ →+* H := (algebraMap R H).comp (algebraMap ℂ R)
  have hzero : ψ.comp (algebraMap P K) =
      (algebraMap R H).comp lpsOriginalJHolomorphicEval.toRingHom := by
    apply RingHom.ext
    intro p
    exact lpsOriginalJFractionEmbedding_polynomial p
  have hscalar (c : ℂ) : ψ (algebraMap ℂ K c) = γ c := by
    have h := RingHom.congr_fun hzero (Polynomial.C c)
    change ψ (algebraMap P K (Polynomial.C c)) =
      algebraMap R H (Polynomial.aeval lpsOriginalJHolomorphic (Polynomial.C c)) at h
    rw [Polynomial.aeval_C] at h
    simpa only [γ, RingHom.comp_apply, Polynomial.C_eq_algebraMap,
      ←IsScalarTower.algebraMap_apply ℂ P K] using h
  have hj : ψ (algebraMap P K Polynomial.X) =
      algebraMap R H lpsOriginalJHolomorphic := by
    have h := RingHom.congr_fun hzero Polynomial.X
    change ψ (algebraMap P K Polynomial.X) =
      algebraMap R H (Polynomial.aeval lpsOriginalJHolomorphic Polynomial.X) at h
    simpa only [Polynomial.aeval_X] using h
  apply RingHom.ext
  intro p
  change ψ ((lpsOriginalReciprocalComplexFieldPolynomialMap N hpos) p) = _
  rw [lpsOriginalReciprocalFieldPolynomialMap_eval,
    Polynomial.hom_eval₂, map_inv₀, hj]
  have hγ : ψ.comp (algebraMap ℂ K) = γ := RingHom.ext hscalar
  rw [hγ]
  rfl
end QEC.Coding.TannerLiftedProduct
