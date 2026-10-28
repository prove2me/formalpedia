-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound_e7f6fb70
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:00:02.951365+00:00
-- url     : https://prove2.me/submissions/dd42827e-d7c6-4d02-8803-2c2573542674
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_e7f6fb70

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    Y.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, _hsub, _hH, hle, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_completion_e7f6fb70 Y hV hY
  omega