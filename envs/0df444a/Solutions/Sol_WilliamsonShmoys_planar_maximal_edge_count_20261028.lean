-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_edge_count_20261028
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:49:23.822985+00:00
-- url     : https://prove2.me/submissions/0fbbe3ee-4e51-4860-893a-d235b8f9382c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_of_drawing
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_lower_bound_of_maximality

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound_of_drawing H hH hCard
  have hLower := WilliamsonShmoys.planar_edge_count_lower_bound_of_maximality H hH hMax hCard
  omega