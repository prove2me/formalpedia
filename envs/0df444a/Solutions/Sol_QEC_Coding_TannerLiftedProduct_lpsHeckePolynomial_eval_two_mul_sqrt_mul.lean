-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_two_mul_sqrt_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:34:43.248382+00:00
-- url     : https://prove2.me/submissions/f12995ca-b483-4ecd-8e90-bdf956b13112

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_add_two
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
    {p : ℝ} (hp : 0 ≤ p) (x : ℝ) : ∀ n : ℕ,
    (lpsHeckePolynomial ℝ p n).eval (2 * Real.sqrt p * x) =
      Real.sqrt p ^ n *
        (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x
  | 0 => by simp
  | 1 => by
      simp
      ring
  | n + 2 => by
      rw [lpsHeckePolynomial_eval_add_two,
        solution hp x (n + 1),
        solution hp x n]
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega,
        Polynomial.Chebyshev.U_add_two]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat, Polynomial.eval_X]
      ring_nf
      rw [Real.sq_sqrt hp]
      norm_num
      ring_nf
      simp
end QEC.Coding.TannerLiftedProduct
