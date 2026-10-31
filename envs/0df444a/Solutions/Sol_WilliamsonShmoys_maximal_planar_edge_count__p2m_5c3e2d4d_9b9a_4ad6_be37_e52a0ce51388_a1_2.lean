-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_5c3e2d4d_9b9a_4ad6_be37_e52a0ce51388_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:35:00.305154+00:00
-- url     : https://prove2.me/submissions/b5fbfeb5-f2ea-4481-a565-f9ff86358444

import Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_drawable_graph

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J) :
    J.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.edge_count_of_edge_maximal_drawable_graph J hDraw hV hMax
