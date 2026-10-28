-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_simple_graph_edge_upper_bound_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:38:06.212+00:00
-- url     : https://prove2.me/submissions/6de957b9-332b-4ebe-9bdb-766791e42487
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 <= Fintype.card V) :
    W.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hsub, _hplanar, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion_v2 W hW hV
  calc
    W.edgeSet.ncard <= H.edgeSet.ncard := Set.ncard_mono hsub
    _ = 3 * Fintype.card V - 6 := hcard