-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval__add_smul_idempotent_187145e154d3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:41:54.02945+00:00
-- url     : https://prove2.me/submissions/7ec1483c-36fc-434a-ba9c-d9d9e4666193

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_add_two
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_mul_polynomial_eval__eq_eval_zero_smul_b42302b28d68
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {A : Type*} [Ring A] [Algebra ℂ A]
    (p d : ℂ) (x e : A)
    (hxe : x * e = 0) (hex : e * x = 0) (hee : e * e = e) : ∀ n : ℕ,
    (lpsHeckePolynomial ℂ p n).eval₂ (algebraMap ℂ A) (x + d • e) =
      (lpsHeckePolynomial ℂ p n).eval₂ (algebraMap ℂ A) x +
        ((lpsHeckePolynomial ℂ p n).eval d -
          (lpsHeckePolynomial ℂ p n).eval 0) • e
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
      rw [lpsHeckePolynomial_add_two]
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul',
        Polynomial.eval₂_X, Polynomial.eval₂_C,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_C]
      rw [
        solution p d x e hxe hex hee (n + 1),
        solution p d x e hxe hex hee n]
      simp [mul_add, add_mul, hxe, hex, hee, sub_mul,
        mul_polynomial_eval₂_eq_eval_zero_smul,
        Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
      simp only [← Algebra.smul_def]
      module
end QEC.Coding.TannerLiftedProduct
