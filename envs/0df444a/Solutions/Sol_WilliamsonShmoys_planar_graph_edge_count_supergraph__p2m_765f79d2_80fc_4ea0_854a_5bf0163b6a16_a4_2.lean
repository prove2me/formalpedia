-- Prove2me | solution 2 for WilliamsonShmoys.planar_graph_edge_count_supergraph__p2m_765f79d2_80fc_4ea0_854a_5bf0163b6a16_a4
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T19:59:31.99891+00:00
-- url     : https://prove2.me/submissions/c435c55d-57e2-4f0a-8583-677bb76221a0

import Theorems.Thm_WilliamsonShmoys_planar_graph_has_exact_edge_count_supergraph
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_graph_has_exact_edge_count_supergraph G hcard hG