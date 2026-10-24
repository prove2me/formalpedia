-- Prove2me | solution 1 for PricingWithTips.theorem_5_2_structured_costs_positive
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T21:28:56.185211+00:00
-- url     : https://prove2.me/submissions/fc8da6af-6f78-43d0-a3b9-0d750305f11c

import Theorems.Thm_PricingWithTips_exists_welfare_optimal_allocation
import Theorems.Thm_PricingWithTips_corollary_4_5_minimum_cost_courier_assignment
import Theorems.Thm_PricingWithTips_structured_costs_optimal_nonfull_has_equilibrium

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem solution [Nonempty B] [Nonempty S] [Nonempty D] :
    ∀ M : Market B S D,
      CourierStoreDecomposable M ∨ CourierBuyerDecomposable M →
        ∃ A p w t, IsWelfareOptimal M A ∧ IsWithTipEquilibrium M A p w t := by
  intro M hstructured
  obtain ⟨A, hoptimal⟩ := exists_welfare_optimal_allocation M
  by_cases hfull : ∀ d, A.CourierWorks d
  · obtain ⟨p, w, t, heq⟩ :=
      corollary_4_5_minimum_cost_courier_assignment M A hfull
        (by intro A' _; exact hoptimal A')
    exact ⟨A, p, w, t, hoptimal, heq⟩
  · obtain ⟨p, w, t, heq⟩ :=
      structured_costs_optimal_nonfull_has_equilibrium M A hstructured hoptimal hfull
    exact ⟨A, p, w, t, hoptimal, heq⟩
