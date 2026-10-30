-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound_face_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:35:40.341888+00:00
-- url     : https://prove2.me/submissions/977507eb-7dd6-44b3-a3fa-0d0961f0d7c7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_core
set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected) (hCard : 3 ≤ Fintype.card V) (f : ℕ)
    (hEuler : G.edgeSet.ncard + 2 = Fintype.card V + f) :
    3 * f ≤ 2 * G.edgeSet.ncard := by
  have hEdge :=
    WilliamsonShmoys.connected_planar_drawing_edge_bound_core G hG hConn hCard
  omega