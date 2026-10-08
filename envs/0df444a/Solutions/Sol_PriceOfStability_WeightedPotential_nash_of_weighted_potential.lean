-- Prove2me | solution 1 for PriceOfStability.WeightedPotential.nash_of_weighted_potential
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-05T10:59:40.370409+00:00
-- url     : https://prove2.me/submissions/cf7bc481-4e67-4f9a-b370-d1b28ebd733c

import Definitions.Def_PriceOfStability_WeightedPotential_Model

open PriceOfStability.WeightedPotential

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

theorem solution (G : WeightedGame ι E) (hw : ∀ i, 0 < G.weight i)
    (hne : ∀ i, (G.strategies i).Nonempty) (Φ : (ι → Finset E) → ℝ)
    (hΦ : ∀ S, IsProfile G S → ∀ i, ∀ T ∈ G.strategies i,
      Φ (Function.update S i T) - Φ S
        = G.weight i * (payment G (Function.update S i T) i - payment G S i)) :
    ∃ S, IsNash G S := by
  classical
  let profiles : Finset (ι → Finset E) := Finset.univ.filter (IsProfile G)
  have hnonempty : profiles.Nonempty := by
    refine ⟨fun i => (hne i).choose, ?_⟩
    simp only [profiles, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun i => (hne i).choose_spec
  obtain ⟨S, hmem, hmin⟩ := Finset.exists_min_image profiles Φ hnonempty
  have hS : IsProfile G S := (Finset.mem_filter.mp hmem).2
  refine ⟨S, hS, ?_⟩
  intro i T hT
  have hnew : IsProfile G (Function.update S i T) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hT
    · simpa [Function.update_of_ne hji] using hS j
  have hbound := hmin (Function.update S i T)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnew⟩)
  have hchange := hΦ S hS i T hT
  have hpos := hw i
  nlinarith

#print axioms solution
