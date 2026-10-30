-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_de26d9eb_6d23_47e8_ab7e_7d74d86b498f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:51:21.037442+00:00
-- url     : https://prove2.me/submissions/c08b6cd5-c630-477c-a2e7-db0f035383e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall N : SimpleGraph V, M <= N -> WilliamsonShmoys.HasPlanarDrawingOn N -> N <= M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  have hupper := WilliamsonShmoys.planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1 M hM hCard
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1 M hM hCard hMax
  omega