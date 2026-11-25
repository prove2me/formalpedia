-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.norm_geom_sum_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:47:56.878044+00:00
-- url     : https://prove2.me/submissions/ab371cfd-f6d1-4056-bb61-08ff60e8832d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormEqOfNormSubLt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_PadicPolynomialApproximation_norm_pow_sub_one_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
open Polynomial Finset
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
theorem _root_.solution {y : ℂ_[l]} (hy : ‖y‖ = 1) (k : ℕ) :
    ‖(∑ i ∈ range k, y ^ i) - k‖ ≤ ‖y - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : (∑ i ∈ range (k + 1), y ^ i) - ((k + 1 : ℕ) : ℂ_[l]) =
        ((∑ i ∈ range k, y ^ i) - k) + (y ^ k - 1) := by
      rw [sum_range_succ]; push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (norm_pow_sub_one_le l hy k))
end ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
