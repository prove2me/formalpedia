-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:02:42.550981+00:00
-- url     : https://prove2.me/submissions/3b55a756-9292-4940-a4c7-27b605e5be7b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_face_count_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConn : G.Connected)
    (hGdraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.connected_planar_drawing_face_count_bound G hConn hGdraw hCard
  omega