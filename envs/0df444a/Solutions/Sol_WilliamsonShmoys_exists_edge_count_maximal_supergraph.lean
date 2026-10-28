-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_count_maximal_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:30:08.271883+00:00
-- url     : https://prove2.me/submissions/f0696a9b-b723-4ffd-a773-90e7792ba4ae

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      P L ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        P M →
        M.edgeSet.ncard ≤ L.edgeSet.ncard := by
  classical
  let s : Set (SimpleGraph V) :=
    {G | K.edgeSet ⊆ G.edgeSet ∧ P G}
  have hs : s.Finite := Set.toFinite s
  have hne : s.Nonempty := by
    refine ⟨K, ?_⟩
    change K.edgeSet ⊆ K.edgeSet ∧ P K
    exact ⟨Set.Subset.rfl, hK⟩
  obtain ⟨L, hLs, hmax⟩ :=
    Set.exists_max_image s (fun G => G.edgeSet.ncard) hs hne
  have hL : K.edgeSet ⊆ L.edgeSet ∧ P L := by
    change L ∈ s at hLs
    exact hLs
  refine ⟨L, hL.1, hL.2, ?_⟩
  intro M hLM hPM
  apply hmax M
  change M ∈ s
  exact ⟨hL.1.trans hLM, hPM⟩
