-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_037368dd_04cc_4345_b537_96bdbb1ae146
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:51:13.463975+00:00
-- url     : https://prove2.me/submissions/781da774-7cca-438c-9161-c0ad0bd53174
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_875ae99f
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_bound_875ae99f

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hup := WilliamsonShmoys.planar_drawing_edge_bound_875ae99f H hdraw hV
  have hlo := WilliamsonShmoys.maximal_drawing_edge_bound_875ae99f
    H hV hdraw hmax
  omega