-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:10:49.122109+00:00
-- url     : https://prove2.me/submissions/97c0767f-4385-43df-9356-8fd7a93ad731
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_count_upper_bound_0319396f
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_0319396f

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hup := WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound_0319396f
    H hH hV
  have hlo := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_0319396f
    H hH hmax hV
  omega