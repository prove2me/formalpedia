-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c39276d2_5642_44b6_8869_8a52171f67f2_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:06:52.295003+00:00
-- url     : https://prove2.me/submissions/6972ddf8-b127-434f-8f79-b621a28e14ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_count_upper_bound__p2m_cb18c991_2437_4ca3_b7e7_f2dc9cdb2f56_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_cb18c991_2437_4ca3_b7e7_f2dc9cdb2f56_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hEdges, hConnected, hHDraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_cb18c991_2437_4ca3_b7e7_f2dc9cdb2f56_a1
      K hDraw (by omega)
  have hBound :=
    WilliamsonShmoys.planar_connected_edge_count_upper_bound__p2m_cb18c991_2437_4ca3_b7e7_f2dc9cdb2f56_a1
      H hHDraw hConnected hV
  omega