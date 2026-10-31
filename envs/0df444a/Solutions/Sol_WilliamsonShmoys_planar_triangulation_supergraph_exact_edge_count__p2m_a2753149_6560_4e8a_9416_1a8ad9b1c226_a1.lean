-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_a2753149_6560_4e8a_9416_1a8ad9b1c226_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:24:09.395369+00:00
-- url     : https://prove2.me/submissions/1df952f3-aecf-45d1-af4c-cdc5336343fd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_exists__p2m_718d0665_f14e_4e4a_9ebf_3d91778b5251_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_718d0665_f14e_4e4a_9ebf_3d91778b5251_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V - 6 = N.edgeSet.ncard := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_718d0665_f14e_4e4a_9ebf_3d91778b5251_a1 M hM
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_718d0665_f14e_4e4a_9ebf_3d91778b5251_a1 N hV hN hmax⟩