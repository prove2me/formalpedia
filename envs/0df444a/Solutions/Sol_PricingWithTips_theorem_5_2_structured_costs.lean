-- Prove2me | solution 1 for PricingWithTips.theorem_5_2_structured_costs
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T19:57:48.076888+00:00
-- url     : https://prove2.me/submissions/94a3cfbb-6081-4843-a64e-c0bc69aaf397

import Theorems.Thm_PricingWithTips_theorem_5_2_structured_costs_positive
import Theorems.Thm_PricingWithTips_theorem_5_2_without_tip_unbounded_loss

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem solution
    [Nonempty B] [Nonempty S] [Nonempty D] :
    (∀ M : Market B S D,
      CourierStoreDecomposable M ∨ CourierBuyerDecomposable M →
        ∃ A p w t, IsWelfareOptimal M A ∧ IsWithTipEquilibrium M A p w t) ∧
    ArbitrarilyLowWithoutTipWelfare := by
  exact ⟨theorem_5_2_structured_costs_positive,
    theorem_5_2_without_tip_unbounded_loss⟩
