-- Prove2me | solution 1 for PricingWithTips.structured_costs_adjusted_matching_of_maximal
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:34:34.994407+00:00
-- url     : https://prove2.me/submissions/a0ab49e2-3860-4fd8-acf4-398ba63da5da

import Theorems.Thm_PricingWithTips_store_full_adjusted_matching_of_optimal
import Theorems.Thm_PricingWithTips_store_nonfull_adjusted_matching_of_maximal
import Theorems.Thm_PricingWithTips_buyer_adjusted_matching_of_maximal

open PricingWithTips

theorem solution {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
    [DecidableEq B] [DecidableEq S] [DecidableEq D]
    [Nonempty B] [Nonempty S] [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hstructured : CourierStoreDecomposable M ∨ CourierBuyerDecomposable M)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (hnonempty : ∃ b, A.assigned b ≠ none)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar) :
    IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by
  rcases hstructured with hstore | hbuyer
  · by_cases hfull : ∀ s, A.Sells s
    · obtain ⟨cBS,cDS,hcost⟩ := hstore
      exact store_full_adjusted_matching_of_optimal
        M A hfull cBS cDS hcost hoptimal uBar hu
    · exact store_nonfull_adjusted_matching_of_maximal
        M A hstore hoptimal hfull hnotfull hnonempty uBar hu
  · exact buyer_adjusted_matching_of_maximal
      M A hbuyer hoptimal hnotfull hnonempty uBar hu
