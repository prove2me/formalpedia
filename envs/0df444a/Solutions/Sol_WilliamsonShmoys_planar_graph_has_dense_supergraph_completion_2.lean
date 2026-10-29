-- Prove2me | solution 2 for WilliamsonShmoys.planar_graph_has_dense_supergraph_completion
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:10:26.120993+00:00
-- url     : https://prove2.me/submissions/c18d50bf-72a9-4f81-b469-1bf720f95469

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L <= M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex L hV hL
