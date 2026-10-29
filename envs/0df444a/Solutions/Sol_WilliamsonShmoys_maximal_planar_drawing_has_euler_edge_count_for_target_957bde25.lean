-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count_for_target_957bde25
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:54:31.373153+00:00
-- url     : https://prove2.me/submissions/cb76501c-f9d6-4dee-9aa0-12155adefa77

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_for_maximal_count_957bde25
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_for_maximal_count_957bde25

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  exact Nat.le_antisymm
    (WilliamsonShmoys.planar_drawing_edge_bound_for_maximal_count_957bde25 L hV hL)
    (WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_for_maximal_count_957bde25 L hV hL hmax)