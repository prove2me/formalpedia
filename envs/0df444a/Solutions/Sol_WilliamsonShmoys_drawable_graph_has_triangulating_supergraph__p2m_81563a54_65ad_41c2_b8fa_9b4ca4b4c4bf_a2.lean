-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_triangulating_supergraph__p2m_81563a54_65ad_41c2_b8fa_9b4ca4b4c4bf_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:08:01.577411+00:00
-- url     : https://prove2.me/submissions/a9131c41-9d16-446b-b18a-49c3e4b1cb0f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_planar_supergraph__p2m_44b3e4a1_3366_4047_b54d_bdbe1bcd0716_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_44b3e4a1_3366_4047_b54d_bdbe1bcd0716_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.drawable_graph_has_maximal_planar_supergraph__p2m_44b3e4a1_3366_4047_b54d_bdbe1bcd0716_a1
      G hG
  refine ⟨H, hGH, hH, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_44b3e4a1_3366_4047_b54d_bdbe1bcd0716_a1
    H hH hmax hV