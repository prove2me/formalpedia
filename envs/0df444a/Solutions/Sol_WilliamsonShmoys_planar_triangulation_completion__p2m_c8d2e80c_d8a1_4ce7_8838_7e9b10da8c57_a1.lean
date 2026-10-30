-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_c8d2e80c_d8a1_4ce7_8838_7e9b10da8c57_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:34:22.409328+00:00
-- url     : https://prove2.me/submissions/05829a6d-fc15-4d5c-938a-de580f6a368e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_25e5c99b_0e98_467d_950b_52f83507dff1_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge__p2m_25e5c99b_0e98_467d_950b_52f83507dff1_a1
import Theorems.Thm_WilliamsonShmoys_completion_from_step_and_bound__p2m_25e5c99b_0e98_467d_950b_52f83507dff1_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  classical
  exact WilliamsonShmoys.completion_from_step_and_bound__p2m_25e5c99b_0e98_467d_950b_52f83507dff1_a1
    HasPlanarDrawingOn
    (by
      intro G hG hV'
      exact WilliamsonShmoys.planar_drawing_edge_bound__p2m_25e5c99b_0e98_467d_950b_52f83507dff1_a1 G hG hV')
    (by
      intro G hG hV' hlt
      exact WilliamsonShmoys.planar_drawing_add_edge__p2m_25e5c99b_0e98_467d_950b_52f83507dff1_a1 G hG hV' hlt)
    H hH hV