-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:10:22.316088+00:00
-- url     : https://prove2.me/submissions/5b0bfdfd-b5cc-45d0-b7a6-57163b05c4e3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_bound
import Theorems.Thm_WilliamsonShmoys_planar_face_count_arithmetic

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler, hPerimeter⟩ :=
    WilliamsonShmoys.planar_drawing_face_count_bound G hV hConnected hG
  exact WilliamsonShmoys.planar_face_count_arithmetic
    (Fintype.card V) G.edgeSet.ncard f hV hEuler hPerimeter