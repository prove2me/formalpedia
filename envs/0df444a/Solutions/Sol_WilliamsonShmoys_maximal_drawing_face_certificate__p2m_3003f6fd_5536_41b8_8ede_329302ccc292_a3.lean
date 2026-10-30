-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_face_certificate__p2m_3003f6fd_5536_41b8_8ede_329302ccc292_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T02:27:21.587168+00:00
-- url     : https://prove2.me/submissions/85fb5e43-8cb2-4bad-b758-737fbc500a2c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_68d7f981_8fd3_430a_af01_9cf213d6ade1_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_68d7f981_8fd3_430a_af01_9cf213d6ade1_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ L : SimpleGraph V,
      G.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ G.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : Nat,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      2 * G.edgeSet.ncard ≤ 3 * f := by
  have hUpper :
      G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_edge_upper_bound__p2m_68d7f981_8fd3_430a_af01_9cf213d6ade1_a1
      G hDraw hV
  have hLower :
      3 * Fintype.card V ≤ G.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_68d7f981_8fd3_430a_af01_9cf213d6ade1_a1
      G hDraw hmax hV
  have hEq : G.edgeSet.ncard + 6 = 3 * Fintype.card V :=
    Nat.le_antisymm hUpper hLower
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega