-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.pow_le_chebyshevU_of_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:00.231301+00:00
-- url     : https://prove2.me/submissions/6e6fb5ed-3eaa-4cd2-8c2a-85993887047f

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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_chebyshevU_nonnegative_and_mul_le_succ
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
    {x : ℝ} (hx : 1 ≤ x) : ∀ n : ℕ,
    x ^ n ≤ (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ]
      calc
        x ^ n * x ≤
            (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x * x := by
          gcongr
          exact solution hx n
        _ = x * (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x := mul_comm _ _
        _ ≤ _ := (chebyshevU_nonnegative_and_mul_le_succ hx n).2
end QEC.Coding.TannerLiftedProduct
