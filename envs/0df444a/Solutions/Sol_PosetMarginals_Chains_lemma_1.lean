-- Prove2me | solution 1 for PosetMarginals.Chains.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:07:22.079996+00:00
-- url     : https://prove2.me/submissions/5f4b1b7a-b801-42d0-8297-295291a85576

import Mathlib
import Definitions.Def_PosetMarginals_Chains_Model

open PosetMarginals.Chains in
theorem solution {α : Type*} [PartialOrder α] [Fintype α] [Nonempty α] :
    IsAntichain (· ≤ ·) {x : α | IsMin x} ∧
      ∀ C : Set α, IsMaxChain (· ≤ ·) C → ∃ x ∈ C, IsMin x := by
  constructor
  · intro x _ y hy hne hxy
    exact hne (le_antisymm hxy (hy hxy))
  · intro C hC
    have hne : C.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      obtain ⟨a⟩ := ‹Nonempty α›
      have hch : IsChain (· ≤ ·) ({a} : Set α) := Set.subsingleton_singleton.isChain
      have := hC.2 hch (by rw [h]; exact Set.empty_subset _)
      rw [h] at this
      exact (Set.singleton_ne_empty a) this.symm
    obtain ⟨c, hc⟩ := hne
    obtain ⟨m, hmC, hmin⟩ := exists_minimal_of_wellFoundedLT (fun x => x ∈ C) ⟨c, hc⟩
    have hleast : ∀ d ∈ C, m ≤ d := by
      intro d hd
      by_cases hmd : m = d
      · exact hmd.le
      · rcases hC.1 hmC hd hmd with h | h
        · exact h
        · exact hmin hd h
    refine ⟨m, hmC, ?_⟩
    intro b hb
    have hch : IsChain (· ≤ ·) (insert b C) := by
      apply hC.1.insert
      intro d hd _
      exact Or.inl (hb.trans (hleast d hd))
    have heq := hC.2 hch (Set.subset_insert b C)
    have hbC : b ∈ C := by rw [heq]; exact Set.mem_insert b C
    exact hleast b hbC
