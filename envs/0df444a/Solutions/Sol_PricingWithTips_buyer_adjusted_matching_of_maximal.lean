-- Prove2me | solution 1 for PricingWithTips.buyer_adjusted_matching_of_maximal
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:39:14.10437+00:00
-- url     : https://prove2.me/submissions/99bdd72f-e14b-4ded-b381-fce531aaaf97

import Theorems.Thm_PricingWithTips_buyer_full_adjusted_matching_of_optimal
import Theorems.Thm_PricingWithTips_buyer_nonfull_adjusted_matching_of_maximal

open PricingWithTips

theorem solution {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
    [DecidableEq B] [DecidableEq S] [DecidableEq D]
    [Nonempty B] [Nonempty S] [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hcost : CourierBuyerDecomposable M)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (hnonempty : ∃ b, A.assigned b ≠ none)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar) :
    IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by
  by_cases hfull : ∀ b, ∃ s d, A.Trades b s d
  · obtain ⟨cBS,cDB,hdecomp⟩ := hcost
    exact buyer_full_adjusted_matching_of_optimal
      M A hfull cBS cDB hdecomp hoptimal uBar hu
  · exact buyer_nonfull_adjusted_matching_of_maximal
      M A hcost hoptimal hfull hnotfull hnonempty uBar hu
