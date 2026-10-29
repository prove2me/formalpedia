-- Prove2me | solution 2 for WilliamsonShmoys.planar_extension_with_sharp_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:16:17.534983+00:00
-- url     : https://prove2.me/submissions/0d2dc7d0-a04a-4c40-8116-845f3bad6d1b

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    exists M : SimpleGraph V, L <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      M.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex L hV hL
