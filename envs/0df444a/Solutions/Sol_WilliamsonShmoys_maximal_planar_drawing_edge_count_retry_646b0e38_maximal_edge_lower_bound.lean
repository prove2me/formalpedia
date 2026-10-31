-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_retry_646b0e38_maximal_edge_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:45:29.189557+00:00
-- url     : https://prove2.me/submissions/69d5c58b-00b9-4c16-bb09-44e3a558fde1

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_c5c6f6ee

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V <= N.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_edge_lower_bound_c5c6f6ee N hV hN hmax
