-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.chebyshevU_nonnegative_and_mul_le_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:46:21.983301+00:00
-- url     : https://prove2.me/submissions/9ad90cf7-4245-4876-839c-3ea3f740efd9

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
    {x : ℝ} (hx : 1 ≤ x) : ∀ n : ℕ,
    0 ≤ (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x ∧
      x * (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x ≤
        (Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval x
  | 0 => by simp; linarith
  | n + 1 => by
      obtain ⟨hn0, hnstep⟩ := solution hx n
      have hnext0 : 0 ≤
          (Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval x :=
        (mul_nonneg (by linarith) hn0).trans hnstep
      constructor
      · exact hnext0
      · rw [show (((n + 1) + 1 : ℕ) : ℤ) = (n : ℤ) + 2 by omega,
          Polynomial.Chebyshev.U_add_two]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_X]
        norm_num only [Nat.cast_add, Nat.cast_one] at hnstep hnext0 ⊢
        have hxx :
            (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x ≤
              x * (Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval x := by
          have hmono :
              (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x ≤
                (Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval x := by
            calc
              (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x ≤
                  x * (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x := by
                nlinarith
              _ ≤ _ := hnstep
          calc
            (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x ≤
                (Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval x := hmono
            _ ≤ x *
                (Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval x := by
              nlinarith
        nlinarith [hxx]
end QEC.Coding.TannerLiftedProduct
