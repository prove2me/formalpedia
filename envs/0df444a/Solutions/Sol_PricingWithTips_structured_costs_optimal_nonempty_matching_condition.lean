-- Prove2me | solution 1 for PricingWithTips.structured_costs_optimal_nonempty_matching_condition
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:15:43.264802+00:00
-- url     : https://prove2.me/submissions/ba30d10d-1572-416f-83b5-fbad812b61d9

import Theorems.Thm_PricingWithTips_optimal_has_maximalCourierUtility
import Theorems.Thm_PricingWithTips_structured_costs_adjusted_matching_of_maximal

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem solution [Nonempty B] [Nonempty S] [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hstructured : CourierStoreDecomposable M ∨ CourierBuyerDecomposable M)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (hnonempty : ∃ b, A.assigned b ≠ none) :
    ∃ uBar : D → ℝ,
      IsMaximalCourierUtility M A uBar ∧
        IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by
  obtain ⟨uBar, hu⟩ := optimal_has_maximalCourierUtility M A hoptimal hnotfull
  exact ⟨uBar, hu,
    structured_costs_adjusted_matching_of_maximal M A hstructured hoptimal
      hnotfull hnonempty uBar hu⟩
