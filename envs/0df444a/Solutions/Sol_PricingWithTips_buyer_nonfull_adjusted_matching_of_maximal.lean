-- Prove2me | solution 1 for PricingWithTips.buyer_nonfull_adjusted_matching_of_maximal
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:49:05.012677+00:00
-- url     : https://prove2.me/submissions/2ad2e685-2ed0-4c9b-8ec3-1e67e63b4e5c

import Theorems.Thm_PricingWithTips_served_buyer_alternatives_le
import Theorems.Thm_PricingWithTips_unmatched_buyer_alternative_le

open PricingWithTips

theorem solution {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
    [DecidableEq B] [DecidableEq S] [DecidableEq D]
    [Nonempty B] [Nonempty S] [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hcost : CourierBuyerDecomposable M)
    (hoptimal : IsWelfareOptimal M A)
    (hbuyer : ¬ ∀ b, ∃ s d, A.Trades b s d)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (hnonempty : ∃ b, A.assigned b ≠ none)
    (uBar : D → ℝ) (hu : IsMaximalCourierUtility M A uBar) :
    IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by
  intro z
  by_cases hnew : ∃ b s, z.assigned b = some s ∧ A.assigned b = none
  · exact unmatched_buyer_alternative_le M A hcost hoptimal hnotfull
      hnonempty uBar hu z hnew
  · obtain ⟨cBS,cDB,hdecomp⟩ := hcost
    apply served_buyer_alternatives_le M A cBS cDB hdecomp hoptimal uBar hu z
    intro b s hz
    cases ha : A.assigned b with
    | none => exact False.elim (hnew ⟨b,s,hz,ha⟩)
    | some sd =>
        rcases sd with ⟨s₀,d₀⟩
        exact ⟨s₀,d₀,ha⟩
