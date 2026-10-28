-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_edge_count_upper_a305a22a
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:00:04.412428+00:00
-- url     : https://prove2.me/submissions/df278a36-624a-40cf-83be-164ed7f2fb65
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_count_upper_connected
import Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_count_upper_disconnected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  classical
  by_cases hc : K.Connected
  · exact WilliamsonShmoys.planar_drawable_edge_count_upper_connected K hV hK hc
  · exact WilliamsonShmoys.planar_drawable_edge_count_upper_disconnected K hV hK hc