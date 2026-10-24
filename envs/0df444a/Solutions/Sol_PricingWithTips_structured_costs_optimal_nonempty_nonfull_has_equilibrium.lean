-- Prove2me | solution 1 for PricingWithTips.structured_costs_optimal_nonempty_nonfull_has_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-20T21:39:57.019288+00:00
-- url     : https://prove2.me/submissions/40feeb2c-fc19-4964-9945-c2c64acb4f3f

import Theorems.Thm_PricingWithTips_lemma_4_4_equilibrium_iff_maximum_weight
import Theorems.Thm_PricingWithTips_structured_costs_optimal_nonempty_matching_condition

open PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem solution [Nonempty B] [Nonempty S] [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hstructured : CourierStoreDecomposable M ∨ CourierBuyerDecomposable M)
    (hoptimal : IsWelfareOptimal M A)
    (hnotfull : ¬ ∀ d, A.CourierWorks d)
    (hnonempty : ∃ b, A.assigned b ≠ none) :
    HasWithTipEquilibriumAt M A := by
  obtain ⟨uBar, hu, hmaximum⟩ :=
    structured_costs_optimal_nonempty_matching_condition
      M A hstructured hoptimal hnotfull hnonempty
  exact (lemma_4_4_equilibrium_iff_maximum_weight M A uBar hu).2 hmaximum
