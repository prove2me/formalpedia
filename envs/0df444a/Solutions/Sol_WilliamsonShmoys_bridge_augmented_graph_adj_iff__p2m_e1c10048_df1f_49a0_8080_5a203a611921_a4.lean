-- Prove2me | solution 1 for WilliamsonShmoys.bridge_augmented_graph_adj_iff__p2m_e1c10048_df1f_49a0_8080_5a203a611921_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:13:50.789346+00:00
-- url     : https://prove2.me/submissions/b1dff5c3-ba5a-4f62-83be-3d454f366a96

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [LinearOrder V]
    (H : SimpleGraph V) (u v : V) (huv : u < v) :
    ∀ a b, a < b →
      ((H ⊔ SimpleGraph.fromRel (fun x y => x = u ∧ y = v)).Adj a b ↔
        H.Adj a b ∨ (a = u ∧ b = v)) := by
  intro a b hab
  simp only [SimpleGraph.sup_adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro (h | ⟨_, hrel⟩)
    · exact Or.inl h
    · rcases hrel with hrel | hrel
      · exact Or.inr hrel
      · have hbad : u < u :=
          lt_trans huv (by simpa [hrel.1, hrel.2] using hab)
        exact (lt_irrefl u hbad).elim
  · rintro (h | ⟨ha, hb⟩)
    · exact Or.inl h
    · right
      refine ⟨ne_of_lt hab, ?_⟩
      exact Or.inl ⟨ha, hb⟩