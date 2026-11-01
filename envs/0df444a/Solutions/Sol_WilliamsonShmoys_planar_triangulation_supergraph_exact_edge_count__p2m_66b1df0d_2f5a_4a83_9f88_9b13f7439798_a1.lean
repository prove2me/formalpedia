-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_66b1df0d_2f5a_4a83_9f88_9b13f7439798_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:50:25.873049+00:00
-- url     : https://prove2.me/submissions/a8718122-95d1-4f0f-b336-0a87342bce79

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_05cc95b8_6993_44ac_b777_7a2cce137e12_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_exact_edge_count__p2m_05cc95b8_6993_44ac_b777_7a2cce137e12_a1

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_05cc95b8_6993_44ac_b777_7a2cce137e12_a1
      L hL
  refine ⟨M, hLM, hM, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_05cc95b8_6993_44ac_b777_7a2cce137e12_a1
    M hcard hM hmax