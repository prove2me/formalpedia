-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_on
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:20:54.630083+00:00
-- url     : https://prove2.me/submissions/9c4ff925-1221-454d-8dfd-fa44f888ab17

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_IsMaximalPlanarOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_on
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_on

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHmax : IsMaximalPlanarOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_edge_count_upper_bound_on H hHmax.1 hV
  have hLower : 3 * Fintype.card V ≤ H.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound_on H hHmax hV
  omega