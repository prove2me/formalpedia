-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_has_triangulated_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:20:42.64839+00:00
-- url     : https://prove2.me/submissions/0e05addf-d94c-450b-b832-c467da5c056d

import Theorems.Thm_WilliamsonShmoys_edge_upper_bound_981f13e1
import Theorems.Thm_WilliamsonShmoys_maximal_edge_lower_bound_981f13e1
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K → H ≤ K → K = H) :
    (H.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  have hUpper := WilliamsonShmoys.edge_upper_bound_981f13e1 H hH hCard
  have hLower := WilliamsonShmoys.maximal_edge_lower_bound_981f13e1 H hH hCard hMax
  omega