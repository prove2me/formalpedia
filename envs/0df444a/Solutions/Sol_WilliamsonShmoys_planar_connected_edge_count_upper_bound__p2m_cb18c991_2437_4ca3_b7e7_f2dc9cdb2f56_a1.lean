-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_count_upper_bound__p2m_cb18c991_2437_4ca3_b7e7_f2dc9cdb2f56_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:12:15.735077+00:00
-- url     : https://prove2.me/submissions/4047dda7-2c6d-41bb-b34f-439a550227f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_triangulation_augmentation__p2m_dd205c68_bd0c_441d_ba83_4d0ce58e6ad4_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hConnected : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hKH, hDrawH, hEdgeLe, hEdgeEq⟩ :=
    WilliamsonShmoys.planar_connected_triangulation_augmentation__p2m_dd205c68_bd0c_441d_ba83_4d0ce58e6ad4_a1
      K hDraw hConnected hV
  omega