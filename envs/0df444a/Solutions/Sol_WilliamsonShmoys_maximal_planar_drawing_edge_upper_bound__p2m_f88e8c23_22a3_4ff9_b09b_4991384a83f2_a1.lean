-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound__p2m_f88e8c23_22a3_4ff9_b09b_4991384a83f2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:17:21.005856+00:00
-- url     : https://prove2.me/submissions/f9abb575-a119-48be-874b-249464419696

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_edge_bound__p2m_a2d35d35_9ed8_4ba3_917d_fe0f629ebdbd_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKplanar, hcard_le, hKedge⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_edge_bound__p2m_a2d35d35_9ed8_4ba3_917d_fe0f629ebdbd_a1
      H hcard hH
  omega