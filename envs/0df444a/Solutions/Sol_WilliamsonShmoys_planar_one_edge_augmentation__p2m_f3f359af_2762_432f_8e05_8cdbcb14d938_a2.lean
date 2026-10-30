-- Prove2me | solution 1 for WilliamsonShmoys.planar_one_edge_augmentation__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:19:18.777229+00:00
-- url     : https://prove2.me/submissions/4eb3b40b-3f0b-4f5f-a84d-dc676523e2f7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_5fed2e6c_fc0c_4ddf_b02b_f52b48f84d02_a1
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_one_edge_step__p2m_5fed2e6c_fc0c_4ddf_b02b_f52b48f84d02_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hEdges : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      H.edgeSet.ncard = G.edgeSet.ncard + 1 ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨K, hGK, hKDraw, hMax⟩ :=
    WilliamsonShmoys.planar_triangulation_completion__p2m_5fed2e6c_fc0c_4ddf_b02b_f52b48f84d02_a1
      G hDraw hCard
  have hStrict : G.edgeSet.ncard < K.edgeSet.ncard := by
    rw [hMax]
    exact hEdges
  exact WilliamsonShmoys.planar_supergraph_one_edge_step__p2m_5fed2e6c_fc0c_4ddf_b02b_f52b48f84d02_a1
    G K hGK hStrict hKDraw