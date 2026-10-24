-- Prove2me | solution 1 for PricingWithTips.store_nonfull_adjusted_matching_of_maximal
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:44:37.004983+00:00
-- url     : https://prove2.me/submissions/cbd3b2ec-c327-47bf-9e16-18036f553df6

import Theorems.Thm_PricingWithTips_sold_store_alternatives_le
import Theorems.Thm_PricingWithTips_unsold_store_alternative_le

open PricingWithTips

theorem solution {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
    [DecidableEq B] [DecidableEq S] [DecidableEq D]
    [Nonempty B] [Nonempty S] [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hcost : CourierStoreDecomposable M)
    (hoptimal : IsWelfareOptimal M A)
    (hstore : ¬ ∀ s, A.Sells s)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (hnonempty : ∃ b, A.assigned b ≠ none)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar) :
    IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by
  intro z
  by_cases hnew : ∃ b s, z.assigned b = some s ∧ ¬ A.Sells s
  · exact unsold_store_alternative_le M A hcost hoptimal hnotfull
      hnonempty uBar hu z hnew
  · obtain ⟨cBS,cDS,hdecomp⟩ := hcost
    apply sold_store_alternatives_le M A cBS cDS hdecomp hoptimal uBar hu z
    intro b s hz
    by_contra hs
    exact hnew ⟨b,s,hz,hs⟩
