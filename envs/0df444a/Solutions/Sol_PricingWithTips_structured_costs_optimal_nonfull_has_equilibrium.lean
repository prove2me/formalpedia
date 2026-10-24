-- Prove2me | solution 1 for PricingWithTips.structured_costs_optimal_nonfull_has_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T21:35:49.467933+00:00
-- url     : https://prove2.me/submissions/05a5841f-be23-42f5-b6d8-159f6aef488c

import Theorems.Thm_PricingWithTips_optimal_empty_has_equilibrium
import Theorems.Thm_PricingWithTips_structured_costs_optimal_nonempty_nonfull_has_equilibrium

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem solution [Nonempty B] [Nonempty S] [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hstructured : CourierStoreDecomposable M ∨ CourierBuyerDecomposable M)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d) :
    HasWithTipEquilibriumAt M A := by
  classical
  by_cases hempty : ∀ b, A.assigned b = none
  · exact optimal_empty_has_equilibrium M A hempty hoptimal
  · push Not at hempty
    exact structured_costs_optimal_nonempty_nonfull_has_equilibrium
      M A hstructured hoptimal hnotfull hempty
