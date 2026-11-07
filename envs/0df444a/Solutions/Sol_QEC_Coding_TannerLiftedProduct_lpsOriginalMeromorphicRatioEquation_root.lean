-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioEquation_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:47:30.205332+00:00
-- url     : https://prove2.me/submissions/f080a57b-48af-4212-b4b0-ce9ff624323b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioCosetPolynomial_eval
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_recovery
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
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
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k)
    (f : ℍ → ℂ) (hf : ∀ τ, A τ = B τ * f τ) (τ : ℍ) :
    (lpsOriginalMeromorphicRatioEquation N k A B).eval₂
      (Polynomial.evalRingHom (lpsOriginalJInvariant τ)) (f τ) = 0 := by
  classical
  let := Fintype.ofFinite (LPSOriginalMeromorphicCosets N)
  have hc : (lpsOriginalMeromorphicRatioCosetPolynomial N k A B τ).eval (f τ) = 0 := by
    rw [lpsOriginalMeromorphicRatioCosetPolynomial_eval]
    simp only [lpsOriginalMeromorphicRatioNorm,ModularForm.mcast_apply,
      ModularForm.coe_norm,Finset.prod_apply]
    apply Finset.prod_eq_zero (Finset.mem_univ (⟦(1 : 𝒮ℒ)⟧))
    simp [SlashInvariantForm.quotientFunc_mk,hf τ,mul_comm]
  have h := congrArg (fun P : Polynomial ℂ => P.eval (f τ))
    (lpsOriginalMeromorphicRatioEquation_recovery N k A B τ)
  rw [Polynomial.eval_mul,Polynomial.eval_C,hc,Polynomial.eval_map] at h
  exact (mul_eq_zero.mp h).resolve_left
    (pow_ne_zero _ (ModularForm.discriminant_ne_zero τ))
end QEC.Coding.TannerLiftedProduct
