-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_52c72b1a_727a_4125_917a_c27d4ca055ae_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:45:58.783688+00:00
-- url     : https://prove2.me/submissions/9c442511-911f-4c88-980a-71096b272440

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_136dc8a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMaximal : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_edge_count_136dc8a1 N hCard hDraw hMaximal
