-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_triangulation_extension_edge_bound_373dcc1c_b5a0_431f_b2a4_dc3190258bf0
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:31:52.658986+00:00
-- url     : https://prove2.me/submissions/90d54000-9816-4169-9707-ca2a8c171b68

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex L hV hL
