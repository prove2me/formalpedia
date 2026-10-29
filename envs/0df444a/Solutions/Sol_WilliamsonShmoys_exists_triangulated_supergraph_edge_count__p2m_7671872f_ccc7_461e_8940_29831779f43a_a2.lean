-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_supergraph_edge_count__p2m_7671872f_ccc7_461e_8940_29831779f43a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-29T04:13:20.558995+00:00
-- url     : https://prove2.me/submissions/93a74af0-40d9-47bf-94b0-e3e5fc509570

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V, H ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_supergraph_2eaf8c58_same_vertex H hCard hH
