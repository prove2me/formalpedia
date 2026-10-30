-- Prove2me | solution 1 for WilliamsonShmoys.drawable_supergraph_edge_count__p2m_3d56d8a6_4977_48bc_b3fc_35028523ea34_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:07:00.034995+00:00
-- url     : https://prove2.me/submissions/e913e83d-48b1-4eac-aa00-4af8bcf503e6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal__p2m_1a5a4a98_d076_4be8_9c0b_d5fb8ab1d149_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_1a5a4a98_d076_4be8_9c0b_d5fb8ab1d149_a1
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hN, hMax⟩ :=
    WilliamsonShmoys.drawable_supergraph_maximal__p2m_1a5a4a98_d076_4be8_9c0b_d5fb8ab1d149_a1
      M hDraw
  have hEdges :=
    WilliamsonShmoys.maximal_drawable_edge_count__p2m_1a5a4a98_d076_4be8_9c0b_d5fb8ab1d149_a1
      N hN hCard hMax
  exact ⟨N, hMN, hN, hEdges⟩