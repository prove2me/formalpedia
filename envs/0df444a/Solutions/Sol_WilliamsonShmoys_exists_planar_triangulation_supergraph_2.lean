-- Prove2me | solution 2 for WilliamsonShmoys.exists_planar_triangulation_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:32:44.825997+00:00
-- url     : https://prove2.me/submissions/fe50e721-f7c2-448a-8f42-5c79bbd16f31

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ H : SimpleGraph V,
      T ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex T hV hT
