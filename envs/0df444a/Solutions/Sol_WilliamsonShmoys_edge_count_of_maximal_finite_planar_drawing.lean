-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_finite_planar_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:50:39.957444+00:00
-- url     : https://prove2.me/submissions/86855970-459a-45f7-bd1f-13f40fc9f3c5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_c797896d_c5f4_44ff_a8ff_d1b689e5dd9a
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_c797896d_c5f4_44ff_a8ff_d1b689e5dd9a

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper :=
    WilliamsonShmoys.planar_drawing_edge_bound_c797896d_c5f4_44ff_a8ff_d1b689e5dd9a M hV hDraw
  have hLower :=
    WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_c797896d_c5f4_44ff_a8ff_d1b689e5dd9a
      M hV hDraw hMax
  omega
