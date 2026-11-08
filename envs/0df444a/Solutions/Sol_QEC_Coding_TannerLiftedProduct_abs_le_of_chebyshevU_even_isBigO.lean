-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.abs_le_of_chebyshevU_even_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:56:13.372568+00:00
-- url     : https://prove2.me/submissions/932af39e-5bda-4093-a858-f4271725f357

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_le_of_forall_gt_evenPow_isBigO
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_pow_even_le_chebyshevU_even


set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (x r : ℝ) (hr : 1 ≤ r)
    (h : ∀ s : ℝ, r < s →
      (fun n : ℕ =>
        (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x) =O[atTop]
          fun n : ℕ => s ^ (2 * n)) :
    |x| ≤ r := by
  by_contra hx
  have hxOne : 1 ≤ |x| := hr.trans (le_of_lt (lt_of_not_ge hx))
  have hPowers : ∀ s : ℝ, r < s →
      (fun n : ℕ => |x| ^ (2 * n)) =O[atTop]
        fun n : ℕ => s ^ (2 * n) := by
    intro s hs
    have hTerm : (fun n : ℕ => |x| ^ (2 * n)) =O[atTop]
        fun n : ℕ =>
          (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x := by
      apply isBigO_of_le atTop
      intro n
      rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg x) _)]
      exact (abs_pow_even_le_chebyshevU_even x n hxOne).trans
        (le_abs_self _)
    exact hTerm.trans (h s hs)
  exact hx (abs_le_of_forall_gt_evenPow_isBigO (x := x)
    (r := r) (by linarith) hPowers)
end QEC.Coding.TannerLiftedProduct
