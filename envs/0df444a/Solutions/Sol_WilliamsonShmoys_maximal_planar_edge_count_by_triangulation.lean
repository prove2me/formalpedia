-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_by_triangulation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:40:01.77011+00:00
-- url     : https://prove2.me/submissions/3ec7ebb1-3e50-4bc5-b2b4-291ab4d3f6f7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_for_maximal_planar_edge_count_by_triangulation_65d9599f
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_for_maximal_planar_edge_count_by_triangulation_65d9599f

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall H' : SimpleGraph V,
      H <= H' -> WilliamsonShmoys.HasPlanarDrawingOn H' -> H' = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planar_edge_upper_bound_for_maximal_planar_edge_count_by_triangulation_65d9599f H hV hH
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound_for_maximal_planar_edge_count_by_triangulation_65d9599f H hV hH hmax
  omega