-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_for_exact_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:52:17.462268+00:00
-- url     : https://prove2.me/submissions/b07a4860-112c-45de-a5b7-6b4e5e00bbcc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_euler_bound_c0c3f643_3cd9_4990_9475_5983163d60d3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  exact WilliamsonShmoys.planar_graph_edge_count_euler_bound_c0c3f643_3cd9_4990_9475_5983163d60d3 H hH hCard