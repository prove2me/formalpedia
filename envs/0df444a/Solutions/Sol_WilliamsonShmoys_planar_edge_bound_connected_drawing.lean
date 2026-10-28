-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_connected_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:28:10.662063+00:00
-- url     : https://prove2.me/submissions/be4cfeb7-cf8b-47ec-accb-3bdc36ae14cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_drawing_face_count_bounds

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    K.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.connected_drawing_face_count_bounds K hV hdraw hconn
  omega