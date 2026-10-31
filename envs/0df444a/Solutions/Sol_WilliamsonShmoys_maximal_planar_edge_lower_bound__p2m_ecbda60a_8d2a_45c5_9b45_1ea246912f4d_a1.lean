-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ecbda60a_8d2a_45c5_9b45_1ea246912f4d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:41:40.052913+00:00
-- url     : https://prove2.me/submissions/409eb179-4fc7-4d36-8d39-be4530115829

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_eaad4d3a_377c_4957_ad25_b7b8620e6c8f_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨M, hLM, hM, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_eaad4d3a_377c_4957_ad25_b7b8620e6c8f_a1
      L hL hCard
  have hEq : M = L := hMax M hLM hM
  rw [hEq] at hCount
  exact le_of_eq hCount