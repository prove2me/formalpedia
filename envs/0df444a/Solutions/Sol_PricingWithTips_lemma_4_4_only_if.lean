-- Prove2me | solution 1 for PricingWithTips.lemma_4_4_only_if
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T22:29:25.99205+00:00
-- url     : https://prove2.me/submissions/e3a5a548-f661-4bf8-a9d8-6b88098f6f4a

import Theorems.Thm_PricingWithTips_equilibrium_has_adjusted_prices
import Theorems.Thm_PricingWithTips_buyerMatching_maximum_of_prices

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem solution [Nonempty D]
    (M : Market B S D) (A : Allocation B S D) (uBar : D → ℝ)
    (hu : IsMaximalCourierUtility M A uBar)
    (heq : HasWithTipEquilibriumAt M A) :
    IsMaximumWeight A.toBuyerMatching (adjustedValue M A uBar) := by
  obtain ⟨p, hp, hbuyer, hunsold⟩ :=
    equilibrium_has_adjusted_prices M A uBar hu heq
  exact buyerMatching_maximum_of_prices A.toBuyerMatching
    (adjustedValue M A uBar) p hp hbuyer hunsold
