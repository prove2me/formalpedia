-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_retry_20261027
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:28:47.858931+00:00
-- url     : https://prove2.me/submissions/dfac176a-154a-4cd4-8d42-d19f1d37cae0

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_c5c6f6ee

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V, N <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = N) :
    3 * Fintype.card V <= N.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_edge_lower_bound_c5c6f6ee N hV hN hmax
