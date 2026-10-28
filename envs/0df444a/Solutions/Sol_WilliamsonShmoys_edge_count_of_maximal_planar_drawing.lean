-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:23:18.390889+00:00
-- url     : https://prove2.me/submissions/4321a450-217a-402c-856a-a78bacd5fed4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_719d44f8_6785_426b_9f1b_0bb1d58add17
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound_719d44f8_6785_426b_9f1b_0bb1d58add17

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V, P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q ≤ P) :
    P.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_edge_count_upper_bound_719d44f8_6785_426b_9f1b_0bb1d58add17 P hV hP
  · exact WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_719d44f8_6785_426b_9f1b_0bb1d58add17 P hV hP hmax