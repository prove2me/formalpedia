-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.neg_one_le_chebyshevT_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:46:15.273011+00:00
-- url     : https://prove2.me/submissions/2f4e7986-21ee-4506-942c-4a10d0bc197f

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
theorem _root_.solution (x : ℝ) (n : ℕ) :
    -1 ≤ (Polynomial.Chebyshev.T ℝ (2 * (n : ℤ))).eval x := by
  by_cases hx : |x| ≤ 1
  · exact neg_le_of_abs_le
      (Polynomial.Chebyshev.abs_eval_T_real_le_one
        (2 * (n : ℤ)) hx)
  · have hAbs : 1 ≤ |x| := le_of_lt (lt_of_not_ge hx)
    by_cases hx0 : 0 ≤ x
    · have hOne : 1 ≤ x := by simpa [abs_of_nonneg hx0] using hAbs
      exact (by norm_num : (-1 : ℝ) ≤ 1).trans
        (Polynomial.Chebyshev.one_le_eval_T_real
          (2 * (n : ℤ)) hOne)
    · have hOne : 1 ≤ -x := by
        rw [← abs_of_nonpos (le_of_not_ge hx0)]
        exact hAbs
      rw [← neg_neg x, Polynomial.Chebyshev.T_eval_neg]
      rw [Int.negOnePow_even _ (even_two_mul (n : ℤ))]
      simpa using ((by norm_num : (-1 : ℝ) ≤ 1).trans
        (Polynomial.Chebyshev.one_le_eval_T_real
          (2 * (n : ℤ)) hOne))
end QEC.Coding.TannerLiftedProduct
