-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_18203136_f8d0_4c28_bbe0_f08319907a9f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:51:21.727338+00:00
-- url     : https://prove2.me/submissions/37e4f719-67f2-4845-98f3-8f1f6d933afe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_connected_completion__p2m_0fddcf0a_fce4_46f9_ad91_85458f71373c_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_has_exact_edge_count_completion__p2m_0fddcf0a_fce4_46f9_ad91_85458f71373c_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hDrawH, hConnH⟩ :=
    WilliamsonShmoys.drawable_graph_has_connected_completion__p2m_0fddcf0a_fce4_46f9_ad91_85458f71373c_a1
      G hDraw hV
  obtain ⟨K, hHK, hDrawK, hCount⟩ :=
    WilliamsonShmoys.connected_planar_drawing_has_exact_edge_count_completion__p2m_0fddcf0a_fce4_46f9_ad91_85458f71373c_a1
      H hDrawH hConnH hV
  exact ⟨K, hGH.trans hHK, hDrawK, hCount⟩