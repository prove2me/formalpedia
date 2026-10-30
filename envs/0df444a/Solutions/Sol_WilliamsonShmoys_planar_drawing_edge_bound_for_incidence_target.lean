-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_for_incidence_target
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:09:55.575589+00:00
-- url     : https://prove2.me/submissions/ac464a60-73aa-4dcf-a7db-f969ad204d8c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_and_face_degree_bound

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G)
    (hconn : G.Connected) (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.planar_drawing_euler_and_face_degree_bound
      G hdraw hconn hV
  omega