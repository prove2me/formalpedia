-- Prove2me | solution 1 for WilliamsonShmoys.edgeMaximal_planar_edge_count_5fac830d_330a_4033_b92d_b2d1f0f7b487
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:28:05.720879+00:00
-- url     : https://prove2.me/submissions/c339e950-23f6-4716-a177-93f08b25578a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_b9b806f7_2f7a_4d09_923b_24ccea114a12
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_lower_bound_b9b806f7_2f7a_4d09_923b_24ccea114a12

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall K : SimpleGraph V,
      M <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.planar_edge_count_upper_bound_b9b806f7_2f7a_4d09_923b_24ccea114a12
      M hV hM
  have hLower :=
    WilliamsonShmoys.edge_maximal_planar_edge_count_lower_bound_b9b806f7_2f7a_4d09_923b_24ccea114a12
      M hV hM hMax
  omega