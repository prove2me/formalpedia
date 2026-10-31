-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_add_edge_exists__p2m_9eb5f952_9b4b_4697_87c0_694ff39636a3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:53:30.007875+00:00
-- url     : https://prove2.me/submissions/9ad4b06a-bb7d-4d51-aa9b-4a79d6ae70ca

import Mathlib

theorem solution {V : Type} [Fintype V] (M N : SimpleGraph V)
    (hMN : M.edgeSet ⊆ N.edgeSet)
    (hcard : M.edgeSet.ncard < N.edgeSet.ncard) :
    ∃ K : SimpleGraph V, M.edgeSet ⊆ K.edgeSet ∧ K.edgeSet ⊆ N.edgeSet ∧
      K.edgeSet.ncard = M.edgeSet.ncard + 1 := by
  classical
  have hex : ∃ e, e ∈ N.edgeSet ∧ e ∉ M.edgeSet := by
    by_contra h
    have hNM : N.edgeSet ⊆ M.edgeSet := by
      intro e heN
      by_contra heM
      exact h ⟨e, heN, heM⟩
    have hle := Set.ncard_mono hNM
    omega
  obtain ⟨e, heN, heM⟩ := hex
  have hdiag : ¬ e.IsDiag := N.not_isDiag_of_mem_edgeSet heN
  let K : SimpleGraph V := M ⊔ SimpleGraph.fromEdgeSet ({e} : Set (Sym2 V))
  have hKset : K.edgeSet = insert e M.edgeSet := by
    ext x
    simp only [K, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet,
      Set.mem_singleton_iff]
    constructor
    · rintro (hxM | ⟨rfl, _⟩)
      · exact Or.inr hxM
      · exact Or.inl rfl
    · rintro (rfl | hxM)
      · exact Or.inr ⟨rfl, hdiag⟩
      · exact Or.inl hxM
  refine ⟨K, ?_, ?_, ?_⟩
  · rw [hKset]
    exact Set.subset_insert e M.edgeSet
  · intro x hx
    rw [hKset] at hx
    rcases Set.mem_insert_iff.mp hx with rfl | hxM
    · exact heN
    · exact hMN hxM
  · rw [hKset, Set.ncard_insert_of_notMem heM]