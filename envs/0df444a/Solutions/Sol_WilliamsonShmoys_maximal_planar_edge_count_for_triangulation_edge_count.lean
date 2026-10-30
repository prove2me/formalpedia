-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:47:32.623056+00:00
-- url     : https://prove2.me/submissions/830ce4c5-6ea1-4385-97c5-63848b361ef8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_2b15add2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_2b15add2
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ H : SimpleGraph V, L ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound_2b15add2 L hV hL
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_2b15add2 L hV hL hmax
  omega