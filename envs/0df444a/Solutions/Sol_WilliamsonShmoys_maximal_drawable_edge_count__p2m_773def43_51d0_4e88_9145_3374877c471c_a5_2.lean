-- Prove2me | solution 2 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_773def43_51d0_4e88_9145_3374877c471c_a5
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:56:14.012891+00:00
-- url     : https://prove2.me/submissions/2c8c437c-03ca-4490-b65f-f895a043bd49

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_edge_count_eq M hCard hDraw hMax
