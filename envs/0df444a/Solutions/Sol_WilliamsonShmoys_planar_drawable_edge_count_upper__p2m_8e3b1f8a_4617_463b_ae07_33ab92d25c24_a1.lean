-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_edge_count_upper__p2m_8e3b1f8a_4617_463b_ae07_33ab92d25c24_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:55:52.854131+00:00
-- url     : https://prove2.me/submissions/1dfb195d-1f21-4a0f-b29c-8d30b91ea3a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph__p2m_12739147_2229_46d9_9b92_e1d48da872e9_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_12739147_2229_46d9_9b92_e1d48da872e9_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn G) (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hSub, hConn, hDrawH⟩ :=
    WilliamsonShmoys.connected_planar_supergraph__p2m_12739147_2229_46d9_9b92_e1d48da872e9_a1
      G hDraw
  exact WilliamsonShmoys.connected_planar_edge_bound__p2m_12739147_2229_46d9_9b92_e1d48da872e9_a1
    G H hSub hConn hDrawH hCard