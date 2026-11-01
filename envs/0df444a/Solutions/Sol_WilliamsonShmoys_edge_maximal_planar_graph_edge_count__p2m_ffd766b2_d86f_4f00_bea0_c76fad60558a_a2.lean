-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_graph_edge_count__p2m_ffd766b2_d86f_4f00_bea0_c76fad60558a_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:29:53.803208+00:00
-- url     : https://prove2.me/submissions/fa346c0f-c33e-4024-b28d-e233afb5d678
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_edge_count_upper__p2m_401bb865_eb7f_4687_8488_019108bab1f9_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_edge_count_lower__p2m_401bb865_eb7f_4687_8488_019108bab1f9_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P ->
      (forall u v, N.Adj u v -> P.Adj u v) -> P = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.edge_maximal_planar_graph_edge_count_upper__p2m_401bb865_eb7f_4687_8488_019108bab1f9_a1 N hN hcard
  have hlower := WilliamsonShmoys.edge_maximal_planar_graph_edge_count_lower__p2m_401bb865_eb7f_4687_8488_019108bab1f9_a1 N hN hcard hmax
  omega