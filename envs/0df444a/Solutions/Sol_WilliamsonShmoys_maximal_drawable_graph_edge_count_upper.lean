-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:54:04.270027+00:00
-- url     : https://prove2.me/submissions/d7fa2541-d6d4-4295-b899-0d4a28c65741
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulating_extension

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨U, hsub, hdraw, hle, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulating_extension T hV hT
  omega