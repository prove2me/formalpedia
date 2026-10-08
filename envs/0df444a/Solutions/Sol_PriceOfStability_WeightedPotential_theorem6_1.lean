-- Prove2me | solution 1 for PriceOfStability.WeightedPotential.theorem6_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-05T10:59:43.517976+00:00
-- url     : https://prove2.me/submissions/2dfe0d85-ac9f-48f3-8e30-6477e446c401

import Theorems.Thm_PriceOfStability_WeightedPotential_potential_change
import Theorems.Thm_PriceOfStability_WeightedPotential_nash_of_weighted_potential

open PriceOfStability.WeightedPotential

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

theorem solution (G : WeightedGame ι E) (hG : G.IsStandard)
    (hspace : ∀ e, (Finset.univ.filter (fun i => e ∈ strategySpace G i)).card ≤ 2) :
    (∃ Φ : (ι → Finset E) → ℝ, ∀ S, IsProfile G S → ∀ i, ∀ T ∈ G.strategies i,
        Φ (Function.update S i T) - Φ S
          = G.weight i * (payment G (Function.update S i T) i - payment G S i)) ∧
      ((∀ i, (G.strategies i).Nonempty) → ∃ S, IsNash G S) := by
  have hchange := PriceOfStability.WeightedPotential.potential_change G hG hspace
  refine ⟨⟨potential G, hchange⟩, ?_⟩
  intro hne
  apply PriceOfStability.WeightedPotential.nash_of_weighted_potential
    G (fun i => lt_of_lt_of_le zero_lt_one (hG.1 i)) hne (potential G) hchange

#print axioms solution
