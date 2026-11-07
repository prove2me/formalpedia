-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.re_trace_even_pow_eq_sum_abs_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:13:21.527843+00:00
-- url     : https://prove2.me/submissions/143f01f5-22f9-4de9-ae08-6aeb93c1f5f7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMomentBound
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_aeval_eq_sum_eval_eigenvalues

set_option autoImplicit false
open Filter Asymptotics
open Polynomial
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (n : ℕ) :
    Complex.re (LinearMap.trace ℂ E (T ^ (2 * n))) =
      ∑ i : Fin (Module.finrank ℂ E),
        |hT.eigenvalues rfl i| ^ (2 * n) := by
  have hTrace := trace_aeval_eq_sum_eval_eigenvalues
    T hT ((Polynomial.X : ℂ[X]) ^ (2 * n))
  simp only [map_pow, aeval_X] at hTrace
  rw [hTrace, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [Polynomial.eval_pow, Polynomial.eval_X]
  rw [pow_mul, pow_mul, sq_abs]
  norm_cast
end QEC.Coding.TannerLiftedProduct
