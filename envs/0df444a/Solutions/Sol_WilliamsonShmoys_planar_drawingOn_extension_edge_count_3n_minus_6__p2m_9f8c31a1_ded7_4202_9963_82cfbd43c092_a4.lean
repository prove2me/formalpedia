-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_extension_edge_count_3n_minus_6__p2m_9f8c31a1_ded7_4202_9963_82cfbd43c092_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T23:06:18.823275+00:00
-- url     : https://prove2.me/submissions/54f4c8d7-c406-4120-ad2d-c853116e2fad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_maximal_extension__p2m_5a949825_f81a_4c8d_a9c0_487ac649892b_a3
import Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_edge_count_3n_minus_6__p2m_5a949825_f81a_4c8d_a9c0_487ac649892b_a3

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hDraw : HasPlanarDrawingOn W)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ X : SimpleGraph V, W ≤ X ∧ HasPlanarDrawingOn X ∧
      X.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨X, hWX, hXDraw, hMax⟩ :=
    WilliamsonShmoys.planar_drawingOn_edge_maximal_extension__p2m_5a949825_f81a_4c8d_a9c0_487ac649892b_a3
      W hDraw
  refine ⟨X, hWX, hXDraw, ?_⟩
  exact WilliamsonShmoys.planar_edge_maximal_edge_count_3n_minus_6__p2m_5a949825_f81a_4c8d_a9c0_487ac649892b_a3
    X hXDraw hCard hMax