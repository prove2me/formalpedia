-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count_data_from_arcs
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:16:45.981629+00:00
-- url     : https://prove2.me/submissions/e26ec2cf-9d4c-47de-92d1-995ee8045320

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_faces
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_from_arcs

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    Exists fun f : Nat =>
      K.edgeSet.ncard + 2 = Fintype.card V + f /\
      3 * f <= 2 * K.edgeSet.ncard := by
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_faces K hconn hdraw
  have hedge :=
    WilliamsonShmoys.planar_simple_graph_edge_bound_from_arcs K hconn hdraw hV
  refine ⟨f, heuler, ?_⟩
  omega