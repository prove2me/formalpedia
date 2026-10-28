-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_drawing_for_completion_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:14:25.84257+00:00
-- url     : https://prove2.me/submissions/aef81cbc-85b8-48ad-83cf-474df41c34cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_count_le_of_planar_drawing
import Theorems.Thm_WilliamsonShmoys_edge_count_ge_of_maximal_planar_drawing

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ L : SimpleGraph V, M ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.edge_count_le_of_planar_drawing M hV hMdraw
  have hlower := WilliamsonShmoys.edge_count_ge_of_maximal_planar_drawing M hV hMdraw hmax
  omega