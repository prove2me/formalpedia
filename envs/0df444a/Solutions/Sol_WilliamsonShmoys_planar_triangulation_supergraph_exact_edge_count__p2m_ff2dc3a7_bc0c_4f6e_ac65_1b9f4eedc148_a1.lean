-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_ff2dc3a7_bc0c_4f6e_ac65_1b9f4eedc148_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:23:08.470921+00:00
-- url     : https://prove2.me/submissions/01637841-bce6-4db7-bfed-81c2eede0933

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_aef33245_cc08_4f0b_a789_a34216bab8c3_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_aef33245_cc08_4f0b_a789_a34216bab8c3_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V - 6 = N.edgeSet.ncard := by
  obtain ⟨N, hMN, hN, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_aef33245_cc08_4f0b_a789_a34216bab8c3_a1
      M hCard hM
  refine ⟨N, hMN, hN, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_aef33245_cc08_4f0b_a789_a34216bab8c3_a1
    N hCard hN hMax