-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_ceffe8f7_0bd7_41ea_898f_3fe9bc8f26e2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:24:37.354927+00:00
-- url     : https://prove2.me/submissions/1dd7994d-7023-45f5-8b29-95dcb385e0fb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_65d0e573_2904_4a2f_b00a_11fd7ff50563_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_65d0e573_2904_4a2f_b00a_11fd7ff50563_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hConn : P.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨Q, hPQ, hQDraw, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_65d0e573_2904_4a2f_b00a_11fd7ff50563_a1
      P hDraw
  refine ⟨Q, hPQ, hQDraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_65d0e573_2904_4a2f_b00a_11fd7ff50563_a1
    Q hQDraw hMax hCard