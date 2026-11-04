-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_edge_count_upper_bound__p2m_f4c5a554_b014_419c_ba42_5bef32be5934_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:20:14.138892+00:00
-- url     : https://prove2.me/submissions/8672e912-e5c7-4f66-86bc-5d875d5015f3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_edge_bound__p2m_fab89fb1_e873_4b82_98f3_cd1985d7426b_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_components_reduce_edge_bound__p2m_fab89fb1_e873_4b82_98f3_cd1985d7426b_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hPlanar : HasPlanarDrawingOn K) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    K.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  let hConnected :
      ∀ {W : Type} [Fintype W] [LinearOrder W] (G : SimpleGraph W),
        3 <= Fintype.card W → G.Connected → HasPlanarDrawingOn G →
          (letI : DecidableRel G.Adj := Classical.decRel G.Adj
           G.edgeFinset.card + 6 <= 3 * Fintype.card W) := by
    intro W hFW hOW G hW hConn hDraw
    exact WilliamsonShmoys.planar_drawing_connected_edge_bound__p2m_fab89fb1_e873_4b82_98f3_cd1985d7426b_a1
      G hW hConn hDraw
  exact WilliamsonShmoys.planar_drawing_components_reduce_edge_bound__p2m_fab89fb1_e873_4b82_98f3_cd1985d7426b_a1
    K hV hPlanar hConnected
