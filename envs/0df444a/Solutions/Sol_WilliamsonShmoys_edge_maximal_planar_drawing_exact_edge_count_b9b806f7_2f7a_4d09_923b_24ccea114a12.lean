-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_drawing_exact_edge_count_b9b806f7_2f7a_4d09_923b_24ccea114a12
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:55:58.259391+00:00
-- url     : https://prove2.me/submissions/f7d0b41e-6f36-4b69-8d6e-76785f2a9d90
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_d42c8f91_ac47_4320_bc80_c3d77a1995cc
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_edge_count_lower_bound_d42c8f91_ac47_4320_bc80_c3d77a1995cc

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall K : SimpleGraph V,
      M <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.edge_maximal_planar_drawing_edge_count_lower_bound_d42c8f91_ac47_4320_bc80_c3d77a1995cc
      M hV hM hMax
  · exact WilliamsonShmoys.planar_drawing_edge_count_upper_bound_d42c8f91_ac47_4320_bc80_c3d77a1995cc
      M hV hM