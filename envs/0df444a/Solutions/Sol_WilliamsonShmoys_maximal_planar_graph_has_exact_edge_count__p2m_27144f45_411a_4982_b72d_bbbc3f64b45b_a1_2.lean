-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_27144f45_411a_4982_b72d_bbbc3f64b45b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:11:47.71896+00:00
-- url     : https://prove2.me/submissions/3d1616c5-0cd3-4e8e-a1c7-9acd37f30896

import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_for_strict_extension_below_bound_2026

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.edge_count_of_maximal_planar_for_strict_extension_below_bound_2026 N hDraw hV hMax
