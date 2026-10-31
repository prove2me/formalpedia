-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_exact_edge_count__p2m_32374ca1_a20e_4fd1_98de_f95812b47536_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:49:38.454003+00:00
-- url     : https://prove2.me/submissions/dc8585db-4420-433c-8641-797e9645e22a

import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulating_supergraph

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.drawable_graph_has_triangulating_supergraph N hCard hDraw
