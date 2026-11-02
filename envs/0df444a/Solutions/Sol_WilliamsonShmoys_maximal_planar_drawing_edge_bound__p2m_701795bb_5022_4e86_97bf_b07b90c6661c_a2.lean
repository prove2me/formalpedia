-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_701795bb_5022_4e86_97bf_b07b90c6661c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:44:51.784201+00:00
-- url     : https://prove2.me/submissions/635ec7c0-e574-4c15-b702-44483ce6ba9c

import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_6f9002e1_e01e_4c8a_bc92_8342a46a38e8_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K -> H <= K -> K <= H)
    [DecidableRel H.Adj] :
    H.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_6f9002e1_e01e_4c8a_bc92_8342a46a38e8_a1
    H hH hcard