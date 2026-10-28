-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:21:36.3847+00:00
-- url     : https://prove2.me/submissions/3ebb4d37-2be3-4f02-a447-e16ec78ee984
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_from_arcs
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound_from_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper :=
    WilliamsonShmoys.planar_drawing_edge_count_upper_bound_from_arcs
      M hV hMdraw
  have hlower :=
    WilliamsonShmoys.maximal_drawable_edge_count_lower_bound_from_completion
      M hV hMdraw hMmax
  omega