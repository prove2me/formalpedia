-- Prove2me | solution 1 for WilliamsonShmoys.euler_face_count_planar_edge_bound_4d0c2802_8f3b_4d79_b31d_d0704c9c8543
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:38:32.345857+00:00
-- url     : https://prove2.me/submissions/a7172386-ba17-4fd6-8312-3c924381f40d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_inequality

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨F, inst, hEuler, hFaces⟩ :=
    WilliamsonShmoys.planar_drawing_face_count_inequality H hH hconn hcard
  omega