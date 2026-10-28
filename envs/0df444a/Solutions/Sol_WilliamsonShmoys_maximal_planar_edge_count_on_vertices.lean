-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_on_vertices
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:43:40.799047+00:00
-- url     : https://prove2.me/submissions/4dad5fa4-ce74-4efd-a655-9428b10aeaa8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_euler_upper_bound_v2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_triangulation_lower_bound_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  have hup := WilliamsonShmoys.planar_edge_count_euler_upper_bound_v2 K hV hK
  have hlo := WilliamsonShmoys.maximal_planar_edge_count_triangulation_lower_bound_v2 K hV hK hmax
  omega