-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.abs_lpsHeckePolynomial_eval_even_le_of_ramanujan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:42:06.687402+00:00
-- url     : https://prove2.me/submissions/c4d3ce93-d38e-4b10-a835-c9b0766e40ea

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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_two_mul_sqrt_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_chebyshevU_even_le_odd
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
    {p : ℝ} (hp : 0 < p) (x : ℝ)
    (hx : |x| ≤ 2 * Real.sqrt p) (n : ℕ) :
    |(lpsHeckePolynomial ℝ p (2 * n)).eval x| ≤
      ((2 * n + 1 : ℕ) : ℝ) * p ^ n := by
  let r := Real.sqrt p
  have hr : 0 < r := Real.sqrt_pos.2 hp
  have hx' : |x / (2 * r)| ≤ 1 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * r)]
    apply (div_le_iff₀ (by positivity : 0 < 2 * r)).2
    simpa [r] using hx
  have hRewrite : 2 * r * (x / (2 * r)) = x := by field_simp
  rw [← hRewrite, lpsHeckePolynomial_eval_two_mul_sqrt_mul hp.le,
    abs_mul, abs_of_nonneg (pow_nonneg hr.le _)]
  have hU := abs_chebyshevU_even_le_odd (x / (2 * r)) hx' n
  calc
    r ^ (2 * n) *
        |(Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval (x / (2 * r))| ≤
        r ^ (2 * n) * ((2 * n + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hU (pow_nonneg hr.le _)
    _ = ((2 * n + 1 : ℕ) : ℝ) * p ^ n := by
      rw [pow_mul, Real.sq_sqrt hp.le]
      ring
end QEC.Coding.TannerLiftedProduct
