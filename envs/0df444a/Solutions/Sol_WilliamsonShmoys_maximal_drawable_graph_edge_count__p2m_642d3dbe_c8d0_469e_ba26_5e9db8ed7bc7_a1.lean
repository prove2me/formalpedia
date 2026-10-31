-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_642d3dbe_c8d0_469e_ba26_5e9db8ed7bc7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:25:33.914983+00:00
-- url     : https://prove2.me/submissions/ba7c419f-812d-4c31-8667-f84cf48512e9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_c298a3e1_504a_4c1d_8a31_03ab929cfe86_a2
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation__p2m_c298a3e1_504a_4c1d_8a31_03ab929cfe86_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hMax : ∀ Q : SimpleGraph V, P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P)
    (hCard : 3 ≤ Fintype.card V) :
    P.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper :=
    WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c298a3e1_504a_4c1d_8a31_03ab929cfe86_a2
      P hDraw hCard
  have hLower : 3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by
    by_contra h
    have hlt : P.edgeSet.ncard < 3 * Fintype.card V - 6 := by omega
    obtain ⟨Q, hPQ, hQne, hQDraw⟩ :=
      WilliamsonShmoys.planar_edge_augmentation__p2m_c298a3e1_504a_4c1d_8a31_03ab929cfe86_a2
        P hDraw hCard hlt
    have hEq : Q = P := hMax Q hPQ hQDraw
    exact hQne hEq
  omega