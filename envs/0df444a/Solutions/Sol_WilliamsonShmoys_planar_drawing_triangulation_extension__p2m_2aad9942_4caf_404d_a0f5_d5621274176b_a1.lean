-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_2aad9942_4caf_404d_a0f5_d5621274176b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:02:30.584625+00:00
-- url     : https://prove2.me/submissions/1d60fc75-806d-4395-bfb1-2d9710d94460

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_b707ad4a_77a6_470e_9bb1_a016cbfcb978_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_b707ad4a_77a6_470e_9bb1_a016cbfcb978_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_b707ad4a_77a6_470e_9bb1_a016cbfcb978_a1
      G hG
  exact ⟨K, hGK, hK,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_b707ad4a_77a6_470e_9bb1_a016cbfcb978_a1
      K hK hmax hV⟩