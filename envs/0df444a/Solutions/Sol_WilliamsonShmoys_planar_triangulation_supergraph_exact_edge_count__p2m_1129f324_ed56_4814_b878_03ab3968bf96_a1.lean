-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_1129f324_ed56_4814_b878_03ab3968bf96_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:39:24.75515+00:00
-- url     : https://prove2.me/submissions/f9cb36a9-e3cb-44ad-9030-c03e92562fd1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_69a4b515_b2d1_4c44_a03e_fe4ffa3a8acf_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_69a4b515_b2d1_4c44_a03e_fe4ffa3a8acf_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_69a4b515_b2d1_4c44_a03e_fe4ffa3a8acf_a1
      M hM
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_69a4b515_b2d1_4c44_a03e_fe4ffa3a8acf_a1
      N hV hN hmax⟩