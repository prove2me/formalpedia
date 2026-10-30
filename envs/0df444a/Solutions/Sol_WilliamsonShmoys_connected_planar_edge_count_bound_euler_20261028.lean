-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_bound_euler_20261028
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:15:26.209006+00:00
-- url     : https://prove2.me/submissions/8aaa3580-2331-4000-bd79-933cddb6edd6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count_edge_bound_20261028
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_of_euler_face_count_20261028

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨F, hEuler, hFaces⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_count_edge_bound_20261028
      G hV hConnected hDraw
  exact WilliamsonShmoys.connected_planar_edge_bound_of_euler_face_count_20261028
    G hV F hEuler hFaces