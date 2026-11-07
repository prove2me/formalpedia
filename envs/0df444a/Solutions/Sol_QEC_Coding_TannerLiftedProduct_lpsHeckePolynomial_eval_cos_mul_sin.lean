-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_cos_mul_sin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:41:58.536109+00:00
-- url     : https://prove2.me/submissions/d326bc26-8479-4169-8818-0b18be6c39c7

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_two_mul_sqrt_mul

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {p : ℝ} (hp : 0 ≤ p) (theta : ℝ) (n : ℕ) :
    (lpsHeckePolynomial ℝ p n).eval
          (2 * Real.sqrt p * Real.cos theta) * Real.sin theta =
      Real.sqrt p ^ n * Real.sin (((n : ℝ) + 1) * theta) := by
  rw [lpsHeckePolynomial_eval_two_mul_sqrt_mul hp]
  calc
    Real.sqrt p ^ n *
          (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (Real.cos theta) *
        Real.sin theta =
        Real.sqrt p ^ n *
          ((Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (Real.cos theta) *
            Real.sin theta) := by ring
    _ = Real.sqrt p ^ n * Real.sin (((n : ℝ) + 1) * theta) := by
      rw [Polynomial.Chebyshev.U_real_cos]
      norm_num
end QEC.Coding.TannerLiftedProduct
