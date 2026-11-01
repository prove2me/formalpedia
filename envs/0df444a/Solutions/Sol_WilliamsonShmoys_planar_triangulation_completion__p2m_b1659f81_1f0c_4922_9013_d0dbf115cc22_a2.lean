-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_b1659f81_1f0c_4922_9013_d0dbf115cc22_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:46:23.216027+00:00
-- url     : https://prove2.me/submissions/2a268bf0-5283-4186-9fb9-53eab6fff0e4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal_extension__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        3 * Fintype.card V - 6 = M.edgeSet.ncard := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.drawable_supergraph_maximal_extension__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1 L hL
  exact ⟨M, hLM, hM, WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1 M hcard hM hmax⟩