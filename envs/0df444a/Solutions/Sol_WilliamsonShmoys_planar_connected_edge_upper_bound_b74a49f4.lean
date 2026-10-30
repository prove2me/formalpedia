-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_upper_bound_b74a49f4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:28:23.773208+00:00
-- url     : https://prove2.me/submissions/61f28526-fbe5-401d-8891-d05d5b4709d2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_euler_face_count_b74a49f4
import Theorems.Thm_WilliamsonShmoys_planar_connected_face_degree_bound_b74a49f4

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hConnected : K.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_connected_euler_face_count_b74a49f4
      K hK hConnected hCard
  have hFace :=
    WilliamsonShmoys.planar_connected_face_degree_bound_b74a49f4
      K hK hConnected hCard f hEuler
  omega