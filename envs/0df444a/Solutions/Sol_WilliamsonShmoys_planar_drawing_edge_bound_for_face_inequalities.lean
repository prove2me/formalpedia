-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_for_face_inequalities
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:52:17.106711+00:00
-- url     : https://prove2.me/submissions/785eb4f7-79d1-44c1-bdc8-b5d67b6f03a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_data_from_arcs

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  have hdata :=
    WilliamsonShmoys.planar_drawing_face_count_data_from_arcs K hconn hdraw hV
  cases hdata with
  | intro f hdata =>
    cases hdata with
    | intro heuler hfaces => omega