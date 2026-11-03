-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_05cc95b8_6993_44ac_b777_7a2cce137e12_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:11:04.406562+00:00
-- url     : https://prove2.me/submissions/803bfa0f-b17e-4fd8-abcc-1f5e04c105d7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_supergraph__p2m_765f79d2_80fc_4ea0_854a_5bf0163b6a16_a4

set_option autoImplicit false

open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hMH, hH, hcount⟩ :=
    WilliamsonShmoys.planar_graph_edge_count_supergraph__p2m_765f79d2_80fc_4ea0_854a_5bf0163b6a16_a4 M hcard hM
  have hHM : H ≤ M := hmax H hMH hH
  have hEq : M = H := le_antisymm hMH hHM
  simpa [hEq] using hcount