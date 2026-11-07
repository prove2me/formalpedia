-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.neg_odd_le_chebyshevU_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:07.72996+00:00
-- url     : https://prove2.me/submissions/a40b9398-5d52-4328-be87-3dad83356a49

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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_neg_one_le_chebyshevT_even
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
theorem _root_.solution (x : ℝ) : ∀ n : ℕ,
    -((2 * n + 1 : ℕ) : ℝ) ≤
      (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x
  | 0 => by simp
  | n + 1 => by
      rw [show (2 * ((n + 1 : ℕ) : ℤ)) = 2 * (n : ℤ) + 2 by omega,
        Polynomial.Chebyshev.U_eq_two_mul_T_add_U]
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_ofNat]
      have hT : -1 ≤
          (Polynomial.Chebyshev.T ℝ (2 * (n : ℤ) + 2)).eval x := by
        rw [show 2 * (n : ℤ) + 2 = 2 * ((n + 1 : ℕ) : ℤ) by omega]
        exact neg_one_le_chebyshevT_even x (n + 1)
      have hU : -((2 * n + 1 : ℕ) : ℝ) ≤
          (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x :=
        solution x n
      calc
        -((2 * (n + 1) + 1 : ℕ) : ℝ) =
            -2 + -((2 * n + 1 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ 2 *
              (Polynomial.Chebyshev.T ℝ (2 * (n : ℤ) + 2)).eval x +
            (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x :=
          add_le_add (by linarith) hU
end QEC.Coding.TannerLiftedProduct
