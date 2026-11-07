-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_even_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:41:59.677218+00:00
-- url     : https://prove2.me/submissions/07216d57-5934-4ec2-ace8-2d1484b7e96f

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_even_scaled_lower_bound

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {p : ℝ} (hp : 0 < p) (x : ℝ) (n : ℕ) :
    -((2 * n + 1 : ℕ) : ℝ) * p ^ n ≤
      (lpsHeckePolynomial ℝ p (2 * n)).eval x := by
  have hsqrt : Real.sqrt p ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have hscaled := lpsHeckePolynomial_eval_even_scaled_lower_bound
    hp.le (x / (2 * Real.sqrt p)) n
  rw [show 2 * Real.sqrt p * (x / (2 * Real.sqrt p)) = x by
    field_simp] at hscaled
  rw [pow_mul, Real.sq_sqrt hp.le] at hscaled
  exact hscaled
end QEC.Coding.TannerLiftedProduct
