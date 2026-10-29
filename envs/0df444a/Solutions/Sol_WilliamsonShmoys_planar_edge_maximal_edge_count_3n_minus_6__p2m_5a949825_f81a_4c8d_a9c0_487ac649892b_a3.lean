-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_maximal_edge_count_3n_minus_6__p2m_5a949825_f81a_4c8d_a9c0_487ac649892b_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T23:20:44.688207+00:00
-- url     : https://prove2.me/submissions/a4f2bca6-93dc-42da-bcee-5f40e79bed2b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_727657a6_98ce_4392_ad63_d05814912170_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V) (hDraw : HasPlanarDrawingOn X)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ Y : SimpleGraph V, X ≤ Y → HasPlanarDrawingOn Y → Y = X) :
    X.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨Y, hXY, hYDraw, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_727657a6_98ce_4392_ad63_d05814912170_a1
      (V := V) X hDraw hCard
  have hEq : Y = X := hMax Y hXY hYDraw
  rw [hEq] at hCount
  exact hCount