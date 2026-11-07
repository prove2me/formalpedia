-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_polynomial_eval__mul_eq_eval_zero_smul_49a5ce81d920
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:41:50.697145+00:00
-- url     : https://prove2.me/submissions/166ea2e0-f6fb-4149-adb7-ce2d9e4a2241

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
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
    (P : ℂ[X]) (x e : A) (hxe : x * e = 0) :
    P.eval₂ (algebraMap ℂ A) x * e = P.eval 0 • e := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [Polynomial.eval₂_add, Polynomial.eval_add, add_mul,
        hP, hQ, add_smul]
  | monomial n a =>
      cases n with
      | zero => simp [Algebra.smul_def]
      | succ n =>
          simp [Polynomial.eval₂_monomial, Polynomial.eval_monomial,
            pow_succ, mul_assoc, hxe]
end QEC.Coding.TannerLiftedProduct
