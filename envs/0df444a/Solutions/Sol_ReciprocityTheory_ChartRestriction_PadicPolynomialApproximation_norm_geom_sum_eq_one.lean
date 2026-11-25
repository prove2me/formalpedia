-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.norm_geom_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:22.804699+00:00
-- url     : https://prove2.me/submissions/8c0c7e5c-d2bb-4fcf-a929-d531b38dc86e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormEqOfNormSubLt
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_PadicPolynomialApproximation_norm_eq_of_norm_sub_lt__a47ddde60030
import Theorems.Thm_ReciprocityTheory_ChartRestriction_PadicPolynomialApproximation_norm_geom_sum_sub_le

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
theorem _root_.solution {y : ℂ_[l]} (hy : ‖y - 1‖ < 1) {m : ℕ} (hm : ‖(m : ℂ_[l])‖ = 1) :
    ‖∑ i ∈ range m, y ^ i‖ = 1 := by
  have hy1 : ‖y‖ = 1 := by
    have := norm_eq_of_norm_sub_lt' l (a := y) (b := 1) (by rwa [norm_one])
    rwa [norm_one] at this
  have := norm_geom_sum_sub_le l hy1 m
  rw [← hm]
  exact norm_eq_of_norm_sub_lt' l (by rw [hm]; exact lt_of_le_of_lt this hy)
end ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation
