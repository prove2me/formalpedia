-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_has_maximal_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:32:24.74865+00:00
-- url     : https://prove2.me/submissions/9f2eb703-55cc-4116-a292-2cafb11dae4f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_b3dab4f4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_b3dab4f4

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M ->
      WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound_b3dab4f4 L hV hL
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_b3dab4f4 L hV hL hmax
  omega