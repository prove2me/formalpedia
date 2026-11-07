-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.abs_pow_even_le_chebyshevU_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:42:07.825605+00:00
-- url     : https://prove2.me/submissions/6baa17da-2ba6-4656-a145-466417a3fbac

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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pow_le_chebyshevU_of_one_le
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
    (x : ℝ) (n : ℕ) (hx : 1 ≤ |x|) :
    |x| ^ (2 * n) ≤
      (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x := by
  have h := pow_le_chebyshevU_of_one_le hx (2 * n)
  by_cases hx0 : 0 ≤ x
  · simpa [abs_of_nonneg hx0] using h
  · rw [show 2 * (n : ℤ) = ((2 * n : ℕ) : ℤ) by omega]
    conv_rhs =>
      rw [← neg_neg x, Polynomial.Chebyshev.U_eval_neg]
    rw [Int.negOnePow_even _ ⟨(n : ℤ), by push_cast; ring⟩]
    simpa [abs_of_nonpos (le_of_not_ge hx0)] using h
end QEC.Coding.TannerLiftedProduct
