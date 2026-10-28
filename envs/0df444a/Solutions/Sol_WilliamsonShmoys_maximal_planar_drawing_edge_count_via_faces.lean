-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_via_faces
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:59:54.698451+00:00
-- url     : https://prove2.me/submissions/92ba14b7-bef7-4c8c-acc6-3a58ed4e7850
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_upper_bound_via_euler_589bf4c0
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_via_triangulation_589bf4c0

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound_via_euler_589bf4c0
      L hV hL
  have hLower :=
    WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_via_triangulation_589bf4c0
      L hV hL hmax
  omega
