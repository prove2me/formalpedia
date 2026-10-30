-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_drawing_has_euler_edge_count_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:13:15.246987+00:00
-- url     : https://prove2.me/submissions/97d45d50-115e-4af8-805e-00061d2a77c8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_v2
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_edge_count_lower_bound_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_drawing_edge_count_upper_bound_v2 L hL hV
  · exact WilliamsonShmoys.edge_maximal_planar_drawing_edge_count_lower_bound_v2
      L hL hmax hV