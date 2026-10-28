-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_connected_b35e3d15_508e_41e1_97ba_51e27adb6431
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:38:43.326143+00:00
-- url     : https://prove2.me/submissions/964f0d0b-4c92-4cc9-8971-fe91a9b1b4fb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_euler_face_certificate
import Theorems.Thm_WilliamsonShmoys_planar_euler_certificate_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.planar_drawing_has_euler_face_certificate H hV hconn hH
  exact WilliamsonShmoys.planar_euler_certificate_edge_bound
    (Fintype.card V) H.edgeSet.ncard f hV heuler hfaces