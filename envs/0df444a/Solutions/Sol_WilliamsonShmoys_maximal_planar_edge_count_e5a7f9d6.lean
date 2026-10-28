-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_e5a7f9d6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:56:14.511489+00:00
-- url     : https://prove2.me/submissions/a73f8972-dedd-4ef0-8c7f-be200b9b3cc2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_via_drawingOn_282b0fbb
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_via_drawingOn_282b0fbb

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → M ≤ L) :
    (L.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_via_drawingOn_282b0fbb L hL hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_via_drawingOn_282b0fbb L hL hCard hmax
  omega