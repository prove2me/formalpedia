-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count__p2m_c20796cc_c576_4992_b291_9784ec70fc6e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:47:05.229047+00:00
-- url     : https://prove2.me/submissions/0d9f3fa7-8d9e-4910-bc79-ea9fdb72c131

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_d7b584f5_f48a_4e68_a764_d92a7993a6d3_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower_bound__p2m_d7b584f5_f48a_4e68_a764_d92a7993a6d3_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    3 * Fintype.card V = L.edgeFinset.card + 6 := by
  have hupper := WilliamsonShmoys.planar_edge_upper_bound__p2m_d7b584f5_f48a_4e68_a764_d92a7993a6d3_a1 L hV hL
  have hlower := WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_d7b584f5_f48a_4e68_a764_d92a7993a6d3_a1 L hV hL hmax
  omega