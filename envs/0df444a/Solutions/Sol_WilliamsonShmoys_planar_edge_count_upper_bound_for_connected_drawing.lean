-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_for_connected_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:20:08.033663+00:00
-- url     : https://prove2.me/submissions/9873eceb-4193-40e0-9a0b-22a7602b7bf0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_has_euler_face_count_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.has_euler_face_count_bound K hK hconn hV
  omega
