-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_bound__p2m_6d23e6d9_3a8b_46d0_86a1_79ef2bae4d90_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:29:26.237807+00:00
-- url     : https://prove2.me/submissions/6ca62fdc-83ab-4b5f-90f2-3e509cf68e2f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_extend_maximal__p2m_a6f95464_e388_4a5e_9ab8_247431a72b86_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_a6f95464_e388_4a5e_9ab8_247431a72b86_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      3 * Fintype.card V - 6 ≤ Q.edgeSet.ncard := by
  obtain ⟨Q, hPQ, hQ, hMax⟩ :=
    WilliamsonShmoys.planar_completion_extend_maximal__p2m_a6f95464_e388_4a5e_9ab8_247431a72b86_a1
      P hP
  have hEdges :=
    WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_a6f95464_e388_4a5e_9ab8_247431a72b86_a1
      Q hCard hQ hMax
  exact ⟨Q, hPQ, hQ, by omega⟩