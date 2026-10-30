-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_fixed_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:38:34.597599+00:00
-- url     : https://prove2.me/submissions/96292ada-9ab4-4f72-a9f5-9b2b7bb6427a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_fixed_vertices
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_fixed_vertices

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hup := WilliamsonShmoys.planar_edge_count_upper_bound_fixed_vertices L hV hDraw
  have hlo := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_fixed_vertices L hV hDraw hmax
  omega