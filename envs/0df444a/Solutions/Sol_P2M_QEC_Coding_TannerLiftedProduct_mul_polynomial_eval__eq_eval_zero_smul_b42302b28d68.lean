-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_mul_polynomial_eval__eq_eval_zero_smul_b42302b28d68
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:46:09.097564+00:00
-- url     : https://prove2.me/submissions/18eec39b-7ee2-4977-8a4b-0d26b4a4d810

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
    (P : ℂ[X]) (x e : A) (hex : e * x = 0) :
    e * P.eval₂ (algebraMap ℂ A) x = P.eval 0 • e := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [Polynomial.eval₂_add, Polynomial.eval_add, mul_add,
        hP, hQ, add_smul]
  | monomial n a =>
      cases n with
      | zero => simp [Algebra.smul_def, Algebra.commutes]
      | succ n =>
          simp only [Polynomial.eval₂_monomial,
            Polynomial.eval_monomial]
          calc
            e * ((algebraMap ℂ A) a * x ^ (n + 1)) =
                (algebraMap ℂ A) a * ((e * x) * x ^ n) := by
              rw [pow_succ', ← mul_assoc,
                ← Algebra.commutes a e]
              simp [mul_assoc]
            _ = 0 := by rw [hex]; simp
            _ = (a * 0 ^ (n + 1)) • e := by simp
end QEC.Coding.TannerLiftedProduct
