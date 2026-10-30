-- Prove2me | solution 1 for WilliamsonShmoys.bridge_add_graph__p2m_02853d91_2027_4c7f_9261_be16db6326ab_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:38:11.957007+00:00
-- url     : https://prove2.me/submissions/fa3e7596-c177-4138-9ab9-36b136e211b4

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (x y : V)
    (hxy : ¬ G.Reachable x y) :
    ∃ N : SimpleGraph V,
      G ≤ N ∧
      (∀ u v, N.Adj u v ↔
        G.Adj u v ∨ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) := by
  have hne : x ≠ y := by
    intro h
    subst y
    exact hxy (SimpleGraph.Reachable.refl x)
  refine ⟨G ⊔ SimpleGraph.edge x y, le_sup_left, ?_⟩
  intro u v
  rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
      · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, hne.symm⟩