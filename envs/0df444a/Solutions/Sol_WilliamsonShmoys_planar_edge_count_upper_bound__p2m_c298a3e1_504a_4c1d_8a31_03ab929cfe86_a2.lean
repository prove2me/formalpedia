-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c298a3e1_504a_4c1d_8a31_03ab929cfe86_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:45:54.973576+00:00
-- url     : https://prove2.me/submissions/3620cbd8-aa6b-4842-8c19-ef86b024de1d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connect_components__p2m_b17d3809_e307_4597_82b6_1d4f1ebd7e38_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_b17d3809_e307_4597_82b6_1d4f1ebd7e38_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hCard : 3 ≤ Fintype.card V) :
    P.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨Q, hPQ, hConn, hQDraw, hEdges⟩ :=
    WilliamsonShmoys.planar_drawing_connect_components__p2m_b17d3809_e307_4597_82b6_1d4f1ebd7e38_a1
      P hDraw
  exact Nat.le_trans hEdges
    (WilliamsonShmoys.connected_planar_edge_bound__p2m_b17d3809_e307_4597_82b6_1d4f1ebd7e38_a1
      Q hQDraw hConn hCard)