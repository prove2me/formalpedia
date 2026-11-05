-- Prove2me | solution 1 for WilliamsonShmoys.triangulate_planar_graph_on_same_vertices__p2m_9bc8f5f5_22dd_4255_9d37_0a6f5ce9c2a7_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:38:28.7252+00:00
-- url     : https://prove2.me/submissions/7f21b016-0895-452c-a93f-67c4c24caf0b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_54b85171_3c84_49d0_b75e_a1ac45808ba4_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_54b85171_3c84_49d0_b75e_a1ac45808ba4_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M ≤ N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hNplanar, hMN, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_54b85171_3c84_49d0_b75e_a1ac45808ba4_a2
      M hplanar
  exact ⟨N, hNplanar, hMN,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_54b85171_3c84_49d0_b75e_a1ac45808ba4_a2
      N hNplanar hmax hcard⟩