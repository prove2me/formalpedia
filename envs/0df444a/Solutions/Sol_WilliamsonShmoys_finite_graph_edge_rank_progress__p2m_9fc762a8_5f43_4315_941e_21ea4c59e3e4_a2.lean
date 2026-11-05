-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_edge_rank_progress__p2m_9fc762a8_5f43_4315_941e_21ea4c59e3e4_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T18:40:09.652237+00:00
-- url     : https://prove2.me/submissions/8a754622-750e-49b1-963d-4913786f0500

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V) (u v : V)
    (hReach : ¬ G.Reachable u v)
    (hEdges : H.edgeSet = G.edgeSet ∪ {Sym2.mk u v}) :
    G.edgeSet.ncard < H.edgeSet.ncard := by
  classical
  have hGuv : ¬ G.Adj u v := fun h => hReach h.reachable
  have he_not : Sym2.mk u v ∉ G.edgeSet := by simpa using hGuv
  have hss : G.edgeSet ⊂ H.edgeSet := by
    rw [hEdges]
    refine (Set.ssubset_iff_of_subset (by intro x hx; exact Or.inl hx)).2
      ⟨Sym2.mk u v, ?_, he_not⟩
    simp
  exact Set.ncard_lt_ncard hss (Set.toFinite _)
