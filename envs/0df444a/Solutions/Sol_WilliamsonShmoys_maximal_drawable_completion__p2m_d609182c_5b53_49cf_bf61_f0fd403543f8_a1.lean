-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_completion__p2m_d609182c_5b53_49cf_bf61_f0fd403543f8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:00:26.249226+00:00
-- url     : https://prove2.me/submissions/92421766-3909-4c5e-99ef-c57b3a0cc839

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists__p2m_d07e54eb_c4bc_460d_b7df_6d44fa14b7ac_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_d07e54eb_c4bc_460d_b7df_6d44fa14b7ac_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hn : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V, ∃ dH : DecidableRel H.Adj,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ G ≤ H ∧
      (letI : DecidableRel H.Adj := dH
       H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨H, dH, hH, hGH, hmax⟩ :=
    WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_d07e54eb_c4bc_460d_b7df_6d44fa14b7ac_a1
      G hG
  have hcard :=
    WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_d07e54eb_c4bc_460d_b7df_6d44fa14b7ac_a1
      H dH hH hn hmax
  exact ⟨H, dH, hH, hGH, hcard⟩