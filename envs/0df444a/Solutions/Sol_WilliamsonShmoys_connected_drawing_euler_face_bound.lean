-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawing_euler_face_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:18:14.341832+00:00
-- url     : https://prove2.me/submissions/55e79eb4-22eb-42da-913b-1fcdbf861ab3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_characteristic
import Theorems.Thm_WilliamsonShmoys_connected_simple_planar_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) :
    exists f : Nat,
      Fintype.card V + f = G.edgeSet.ncard + 2 /\
      3 * f <= 2 * G.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.connected_drawing_euler_characteristic G hdraw hconn hV
  have hEdges :=
    WilliamsonShmoys.connected_simple_planar_edge_bound G hdraw hconn hV
  refine ⟨f, hEuler, ?_⟩
  omega
