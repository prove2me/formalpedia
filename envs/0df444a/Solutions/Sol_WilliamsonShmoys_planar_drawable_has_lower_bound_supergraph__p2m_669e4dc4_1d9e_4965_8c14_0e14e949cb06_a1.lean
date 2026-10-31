-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_has_lower_bound_supergraph__p2m_669e4dc4_1d9e_4965_8c14_0e14e949cb06_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:03:40.37371+00:00
-- url     : https://prove2.me/submissions/027ae2f5-b00d-4e93-8e35-e1acbb95b455

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edgeMaximal_planar_supergraph_same_vertex__p2m_3ee6bacb_2bd6_4aaa_b06f_7ea404afd915_a1
import Theorems.Thm_WilliamsonShmoys_edgeMaximal_planar_graph_lower_bound_same_vertex__p2m_3ee6bacb_2bd6_4aaa_b06f_7ea404afd915_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨H, hGH, hH, hMax⟩ :=
    WilliamsonShmoys.exists_edgeMaximal_planar_supergraph_same_vertex__p2m_3ee6bacb_2bd6_4aaa_b06f_7ea404afd915_a1 G hG
  exact ⟨H, hGH, hH,
    WilliamsonShmoys.edgeMaximal_planar_graph_lower_bound_same_vertex__p2m_3ee6bacb_2bd6_4aaa_b06f_7ea404afd915_a1 H hH hMax hCard⟩