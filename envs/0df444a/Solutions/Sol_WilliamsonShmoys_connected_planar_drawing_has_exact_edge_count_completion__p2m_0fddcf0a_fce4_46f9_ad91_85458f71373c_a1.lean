-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_has_exact_edge_count_completion__p2m_0fddcf0a_fce4_46f9_ad91_85458f71373c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:57:37.371907+00:00
-- url     : https://prove2.me/submissions/d4f175e2-77a6-442e-b52e-426c665dec7a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_has_maximal_extension__p2m_7c31868e_1a48_4873_9b3b_c3421781b09b_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_exact_edge_count__p2m_7c31868e_1a48_4873_9b3b_c3421781b09b_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hGK, hDrawK, hMax⟩ :=
    WilliamsonShmoys.connected_planar_drawing_has_maximal_extension__p2m_7c31868e_1a48_4873_9b3b_c3421781b09b_a1
      G hDraw
  refine ⟨K, hGK, hDrawK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count__p2m_7c31868e_1a48_4873_9b3b_c3421781b09b_a1
    K hDrawK hMax hV