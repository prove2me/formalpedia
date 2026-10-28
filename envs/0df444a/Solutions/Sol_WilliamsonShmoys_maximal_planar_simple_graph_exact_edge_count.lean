-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_simple_graph_exact_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:35:50.499652+00:00
-- url     : https://prove2.me/submissions/2629fdf5-07e4-4a59-87db-7f9a173b9734
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_drawing_for_exact_count
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_for_exact_count
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_bound_of_drawing_for_exact_count
    H hH hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_lower_bound_for_exact_count
    H hH hMax hCard
  omega