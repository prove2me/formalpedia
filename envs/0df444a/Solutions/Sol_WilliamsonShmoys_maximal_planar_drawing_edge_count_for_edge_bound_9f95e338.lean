-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_for_edge_bound_9f95e338
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:06:06.160572+00:00
-- url     : https://prove2.me/submissions/b03381f7-a0ee-41ff-b473-8a7a94045c85
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_9f95e338
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_9f95e338

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn T) (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper : T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_drawing_edge_upper_bound_9f95e338 T hdraw hV
  have hlower : 3 * Fintype.card V ≤ T.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_9f95e338 T hdraw hV hmax
  omega