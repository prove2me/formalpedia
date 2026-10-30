-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_incidence_bound_from_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:54:08.988843+00:00
-- url     : https://prove2.me/submissions/74c6db91-8218-4dc8-b113-16d8a87694e5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_for_incidence_target

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) (f : Nat)
    (hEuler : Fintype.card V + f = G.edgeSet.ncard + 2) :
    3 * f <= 2 * G.edgeSet.ncard := by
  have hbound :=
    WilliamsonShmoys.planar_drawing_edge_bound_for_incidence_target
      G hdraw hconn hV
  omega