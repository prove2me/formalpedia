-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_with_triangulated_edge_count__p2m_ff88384e_13a7_4e55_8777_790088f23a4a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:42:38.959422+00:00
-- url     : https://prove2.me/submissions/ab517df2-bcc3-4bc9-8fc2-b717dd99f997

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_4c675a48_b2e7_41d9_8987_0c6f38bd3a34_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_4c675a48_b2e7_41d9_8987_0c6f38bd3a34_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_4c675a48_b2e7_41d9_8987_0c6f38bd3a34_a1 L hL
  exact ⟨M, hLM, hM,
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_4c675a48_b2e7_41d9_8987_0c6f38bd3a34_a1 M hcard hM hmax⟩