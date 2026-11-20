-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFrobeniusPair_subring_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T11:52:08.865058+00:00
-- url     : https://prove2.me/submissions/c2b3d7fc-927b-410d-855c-11149e47dc3e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
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
open scoped TensorProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {K : Type*} [Field K] (p : ℕ) (S : Subring (K × K))
    (hfirst : ∀ a : K, (a, a^p) ∈ S)
    (hsecond : ∀ a : K, (a^p, a) ∈ S)
    (u : K) (hu : (u^p)^p ≠ u) : S = ⊤ := by
  let d := u - (u^p)^p
  have hd : d ≠ 0 := sub_ne_zero.mpr hu.symm
  have h10 : ((1 : K), (0 : K)) ∈ S := by
    have h := S.mul_mem (hfirst d⁻¹) (S.sub_mem (hfirst u) (hsecond (u^p)))
    have he : (d⁻¹, (d⁻¹)^p) * ((u, u^p) - ((u^p)^p, u^p)) =
        ((1 : K), (0 : K)) := by
      apply Prod.ext
      · change d⁻¹ * (u - (u^p)^p) = 1
        exact inv_mul_cancel₀ hd
      · simp
    exact he ▸ h
  have h01 : ((0 : K), (1 : K)) ∈ S := by
    have h := S.sub_mem S.one_mem h10
    have he : (1 : K × K) - ((1 : K), (0 : K)) = ((0 : K), (1 : K)) := by
      ext <;> simp
    exact he ▸ h
  apply top_unique
  intro x _hx
  have h := S.add_mem (S.mul_mem (hfirst x.1) h10) (S.mul_mem (hsecond x.2) h01)
  have he : (x.1, x.1^p) * ((1 : K), (0 : K)) +
      (x.2^p, x.2) * ((0 : K), (1 : K)) = x := by
    ext <;> simp
  exact he ▸ h
end QEC.Coding.TannerLiftedProduct
