-- Prove2me | solution 1 for WilliamsonShmoys.finite_connected_vertex_partition__p2m_7d0b953f_c62a_470f_b8ef_9a25b50c3ad5_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:00:07.382559+00:00
-- url     : https://prove2.me/submissions/b67d3bd2-4da0-41b1-82e7-2329f9732566

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) :
    ∃ parts : Finset (Finset V),
      (∀ s ∈ parts, s.Nonempty ∧ (K.induce (↑s : Set V)).Connected) ∧
      (∀ v, ∃ s ∈ parts, v ∈ s) ∧
      (∀ s ∈ parts, ∀ t ∈ parts, s ≠ t → Disjoint s t) ∧
      (∀ u v, K.Adj u v → ∃ s ∈ parts, u ∈ s ∧ v ∈ s) := by
  classical
  let parts : Finset (Finset V) :=
    Finset.univ.image fun c : K.ConnectedComponent => c.supp.toFinset
  refine ⟨parts, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases Finset.mem_image.mp hs with ⟨c, -, rfl⟩
    constructor
    · obtain ⟨v, hv⟩ := c.nonempty_supp
      exact ⟨v, by simpa using hv⟩
    · have hcoe : (c.supp.toFinset : Set V) = c.supp := by
        ext x
        simp
      change (K.induce (c.supp.toFinset : Set V)).Connected
      rw [hcoe]
      exact c.connected_toSimpleGraph
  · intro v
    refine ⟨(K.connectedComponentMk v).supp.toFinset, ?_, ?_⟩
    · exact Finset.mem_image.mpr
        ⟨K.connectedComponentMk v, Finset.mem_univ _, rfl⟩
    · simp [SimpleGraph.ConnectedComponent.mem_supp_iff]
  · intro s hs t ht hne
    rcases Finset.mem_image.mp hs with ⟨c, -, rfl⟩
    rcases Finset.mem_image.mp ht with ⟨d, -, rfl⟩
    rw [Finset.disjoint_left]
    intro v hv hw
    have hcd : c = d :=
      SimpleGraph.ConnectedComponent.eq_of_common_vertex
        (by simpa using hv) (by simpa using hw)
    exact hne (by simpa [hcd])
  · intro u v hadj
    refine ⟨(K.connectedComponentMk u).supp.toFinset, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr
        ⟨K.connectedComponentMk u, Finset.mem_univ _, rfl⟩
    · simp [SimpleGraph.ConnectedComponent.mem_supp_iff]
    · have huv : K.connectedComponentMk u = K.connectedComponentMk v :=
        SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
      simp [SimpleGraph.ConnectedComponent.mem_supp_iff, huv]
