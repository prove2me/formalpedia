-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_triangulation_edge_count_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:28:24.912618+00:00
-- url     : https://prove2.me/submissions/610d2f89-59b2-43db-bf07-6339b185cdaf

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_maximal_target
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_target

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_drawing_edge_count_upper_bound_maximal_target H hH hV
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_target H hH hV hMax
  omega