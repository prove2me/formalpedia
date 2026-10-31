-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_completion_exact_edge_count__p2m_eb21a977_2509_4ef4_8e83_e4c522788ebf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:45:25.037552+00:00
-- url     : https://prove2.me/submissions/18512f88-6c6a-45fd-92b9-b433ef1a2bba

import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulating_supergraph

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.drawable_graph_has_triangulating_supergraph M hCard hDraw
