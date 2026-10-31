-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_33f2abb6_4890_4032_9845_f9099e3af4d0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:06:49.894287+00:00
-- url     : https://prove2.me/submissions/a22dee64-9061-4ffa-82be-e1aa36af1987

import Theorems.Thm_WilliamsonShmoys_finite_predicate_maximal_supergraph_exists__p2m_a41ba058_0926_4932_8131_302826679a62_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_a41ba058_0926_4932_8131_302826679a62_a2
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K := by
  exact WilliamsonShmoys.finite_predicate_maximal_supergraph_exists__p2m_a41ba058_0926_4932_8131_302826679a62_a2
    G WilliamsonShmoys.HasPlanarDrawingOn hG
    (by
      intro A B hAB hB
      exact WilliamsonShmoys.planar_drawing_subgraph__p2m_a41ba058_0926_4932_8131_302826679a62_a2 A B hAB hB)