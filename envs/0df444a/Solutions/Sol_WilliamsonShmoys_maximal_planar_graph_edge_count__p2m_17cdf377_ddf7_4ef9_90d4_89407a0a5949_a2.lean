-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_17cdf377_ddf7_4ef9_90d4_89407a0a5949_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:11:22.784196+00:00
-- url     : https://prove2.me/submissions/4dbfa3a4-35f9-452e-9899-702bcd0a1d27

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_upper_bound__p2m_fbb67fbe_1ef6_4f56_af7e_e7b6a6ede470_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_fbb67fbe_1ef6_4f56_af7e_e7b6a6ede470_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    M.edgeFinset.card = 3 * Fintype.card V - 6 := by
  have hupper :=
    WilliamsonShmoys.maximal_planar_graph_edge_upper_bound__p2m_fbb67fbe_1ef6_4f56_af7e_e7b6a6ede470_a1
      M dM hM hcard
  have hlower :=
    WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_fbb67fbe_1ef6_4f56_af7e_e7b6a6ede470_a1
      M dM hM hcard hmax
  omega