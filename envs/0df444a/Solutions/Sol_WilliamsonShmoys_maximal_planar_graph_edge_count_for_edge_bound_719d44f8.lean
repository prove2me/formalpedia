-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_for_edge_bound_719d44f8
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:58:22.66868+00:00
-- url     : https://prove2.me/submissions/d4cecce0-62a1-4d8b-a0e9-92301059462d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound_719d44f8
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_719d44f8

set_option autoImplicit false

/-- The Euler upper bound and the maximality lower bound force equality. -/
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.maximal_planar_edge_count_upper_bound_719d44f8 H hV hH
  · exact WilliamsonShmoys.maximal_planar_edge_count_lower_bound_719d44f8 H hV hH hmax