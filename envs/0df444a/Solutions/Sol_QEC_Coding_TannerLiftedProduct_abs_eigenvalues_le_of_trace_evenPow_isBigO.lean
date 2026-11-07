-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.abs_eigenvalues_le_of_trace_evenPow_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:46:14.537468+00:00
-- url     : https://prove2.me/submissions/9e43f07a-e84c-4e42-a555-ecf20bff6b56

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMomentBound
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_re_trace_even_pow_eq_sum_abs_eigenvalues
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_le_of_evenMoment_isBigO


set_option autoImplicit false
open Filter Asymptotics
open Polynomial
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    {r : ℝ} (hr : 0 ≤ r)
    (hTrace : ∀ s : ℝ, r < s →
      (fun n : ℕ =>
        Complex.re (LinearMap.trace ℂ E (T ^ (2 * n)))) =O[atTop]
          fun n : ℕ => s ^ (2 * n)) :
    ∀ i : Fin (Module.finrank ℂ E),
      |hT.eigenvalues rfl i| ≤ r := by
  apply abs_le_of_evenMoment_isBigO
    (eigenvalue := hT.eigenvalues rfl) hr
  intro s hrs
  simpa only [re_trace_even_pow_eq_sum_abs_eigenvalues T hT] using
    hTrace s hrs
end QEC.Coding.TannerLiftedProduct
