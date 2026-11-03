-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation_edge_count__p2m_4c7ec41a_7a94_4be9_ac1a_23f63e19fba0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:08:51.384203+00:00
-- url     : https://prove2.me/submissions/cc2e4f39-c7df-4fee-888c-ccc19bb1f657

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_d9484fdc_deb9_4095_abe2_5d54d805080e_a1
import Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_graph_edge_count__p2m_d9484fdc_deb9_4095_abe2_5d54d805080e_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        (letI : DecidableRel H.Adj := Classical.decRel H.Adj
         H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_d9484fdc_deb9_4095_abe2_5d54d805080e_a1 G hG
  have hcount :=
    WilliamsonShmoys.inclusion_maximal_planar_graph_edge_count__p2m_d9484fdc_deb9_4095_abe2_5d54d805080e_a1 H hcard hH hmax
  exact ⟨H, hGH, hH, hcount⟩