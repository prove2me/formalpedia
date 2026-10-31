-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_6d3b2982_65b7_41de_b042_0682b8cb7f57_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:14:45.944108+00:00
-- url     : https://prove2.me/submissions/f142052d-5f0b-41ef-8423-7ee5713450b3

import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_bound__p2m_6d23e6d9_3a8b_46d0_86a1_79ef2bae4d90_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hMax : ∀ Q : SimpleGraph V,
      P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q →
        Q.edgeSet.ncard ≤ P.edgeSet.ncard) :
    3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by
  obtain ⟨Q, hPQ, hQ, hBound⟩ :=
    WilliamsonShmoys.planar_completion_edge_bound__p2m_6d23e6d9_3a8b_46d0_86a1_79ef2bae4d90_a1
      P hCard hP
  exact le_trans hBound (hMax Q hPQ hQ)