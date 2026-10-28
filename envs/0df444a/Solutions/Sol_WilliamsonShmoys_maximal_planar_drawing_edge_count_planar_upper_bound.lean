-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_planar_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:05:56.019428+00:00
-- url     : https://prove2.me/submissions/4c238a97-33d7-461f-bb12-605ee19f7812
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_connected_drawing
import Theorems.Thm_WilliamsonShmoys_planar_drawing_restrict_induced
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_connected_induced_components

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  classical
  apply WilliamsonShmoys.planar_edge_bound_from_connected_induced_components K hV
  intro W hFW hW hconn
  letI : Fintype W := hFW
  have hdrawW : WilliamsonShmoys.HasPlanarDrawingOn (K.induce W) :=
    WilliamsonShmoys.planar_drawing_restrict_induced K hdraw W hFW
  exact WilliamsonShmoys.planar_edge_bound_connected_drawing
    (K.induce W) hW hdrawW hconn