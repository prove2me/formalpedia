-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_1fc721c4_d4d8_4a3d_8e5b_8d3e1462bbc6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:41:33.641997+00:00
-- url     : https://prove2.me/submissions/aa67b51a-a4bf-414e-b79c-eb98f51d1cf8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound_completion__p2m_3dc4c4ae_a795_4a3d_94e8_45085e13492e_a1

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ H : SimpleGraph V, G ≤ H → HasPlanarDrawingOn H → H = G) :
    3 * Fintype.card V - 6 ≤ G.edgeSet.ncard := by
  obtain ⟨H, hGH, hH, hBound⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_edge_bound_completion__p2m_3dc4c4ae_a795_4a3d_94e8_45085e13492e_a1
      G hG hCard
  have hEq : H = G := hMax H hGH hH
  simpa [hEq] using hBound