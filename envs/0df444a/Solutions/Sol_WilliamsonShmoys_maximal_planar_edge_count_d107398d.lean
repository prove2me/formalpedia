-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_d107398d
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:00:20.04004+00:00
-- url     : https://prove2.me/submissions/affc9ef0-f1b1-44d1-b8b6-0a0c19ec4489

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_afa305d5
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_afa305d5

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall J : SimpleGraph V, H <= J ->
      WilliamsonShmoys.HasPlanarDrawingOn J -> J = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound_afa305d5 H hDraw hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_afa305d5 H hDraw hCard hMax
  omega