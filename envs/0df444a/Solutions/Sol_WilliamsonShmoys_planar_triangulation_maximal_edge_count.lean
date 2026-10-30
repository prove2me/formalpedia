-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_maximal_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:31:56.711207+00:00
-- url     : https://prove2.me/submissions/33e30d39-07a8-4710-9077-7e1f3907dd2e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_from_euler_c132589d_retry3
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count_lower_from_triangulation_c132589d_retry3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      (∀ u v, L.Adj u v → M.Adj u v) →
      HasPlanarDrawingOn M →
      ∀ u v, M.Adj u v → L.Adj u v) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.planar_drawing_edge_bound_from_euler_c132589d_retry3
      L hCard hDraw
  have hLower :=
    WilliamsonShmoys.maximal_drawing_edge_count_lower_from_triangulation_c132589d_retry3
      L hCard hDraw hMax
  omega