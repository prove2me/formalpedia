-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_136dc8a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:12:48.237823+00:00
-- url     : https://prove2.me/submissions/0fd8c9a9-6a60-4669-b7f3-5e6f0c93f22d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound_via_drawing_v3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_via_drawing_v3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper : N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_planar_edge_upper_bound_via_drawing_v3 N hV hN
  have hLower : 3 * Fintype.card V ≤ N.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound_via_drawing_v3 N hV hN hmax
  omega