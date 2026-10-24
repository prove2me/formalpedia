-- Prove2me | solution 1 for PricingWithTips.corollary_4_5_minimum_cost_courier_assignment
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T20:30:42.957639+00:00
-- url     : https://prove2.me/submissions/189989f2-c339-4e5b-aca0-fcef395e15a0

import Theorems.Thm_PricingWithTips_minimum_cost_full_assignment_has_plan
import Theorems.Thm_PricingWithTips_full_courier_plan_has_equilibrium

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem solution [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hfull : ∀ d, A.CourierWorks d)
    (hminimum : ∀ A' : Allocation B S D,
      (∀ b, (A'.assigned b).map Prod.fst = (A.assigned b).map Prod.fst) →
        welfare M A' ≤ welfare M A) :
    HasWithTipEquilibriumAt M A := by
  obtain ⟨w, hplan⟩ := minimum_cost_full_assignment_has_plan M A hfull hminimum
  exact full_courier_plan_has_equilibrium M A hfull w hplan
