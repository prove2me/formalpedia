-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_a7de67a5_633c_46b0_b277_259b7a4818e8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:23:45.484192+00:00
-- url     : https://prove2.me/submissions/5053aca4-2eb5-4f00-adcf-b743b2ec6d06

import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_edge_count__p2m_c7da917f_6656_4021_9748_8f0ed1f8ec40_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  obtain ⟨H, hLH, hH, hcount⟩ :=
    WilliamsonShmoys.maximal_planar_completion_edge_count__p2m_c7da917f_6656_4021_9748_8f0ed1f8ec40_a1
      L hL hV
  have hEq : H = L := hmax H hLH hH
  rw [hEq] at hcount
  exact hcount.symm