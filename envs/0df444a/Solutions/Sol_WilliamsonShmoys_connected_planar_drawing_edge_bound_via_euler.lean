-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound_via_euler
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:03:35.495064+00:00
-- url     : https://prove2.me/submissions/78f1d43d-031b-438d-9a60-445b7fa6a62e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_data
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_euler_face_data

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G)
    (hconn : G.Connected) (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler, hFaceDegrees⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_data G hdraw hconn hV
  exact WilliamsonShmoys.edge_bound_of_euler_face_data
    (Fintype.card V) G.edgeSet.ncard f hEuler hFaceDegrees hV