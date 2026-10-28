-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_drawing_fddd844c
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:07:37.255357+00:00
-- url     : https://prove2.me/submissions/72c84ac7-1ba6-4a87-9889-f3b3ce822c64
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_fddd844c
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_fddd844c

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N →
      M.edgeSet ⊆ N.edgeSet → N.edgeSet = M.edgeSet) :
    3 * (Fintype.card V : Int) - 6 = (M.edgeSet.ncard : Int) := by
  apply le_antisymm
  · exact WilliamsonShmoys.maximal_planar_edge_count_lower_bound_fddd844c M hM hCard hMax
  · exact WilliamsonShmoys.planar_edge_count_upper_bound_fddd844c M hM hCard