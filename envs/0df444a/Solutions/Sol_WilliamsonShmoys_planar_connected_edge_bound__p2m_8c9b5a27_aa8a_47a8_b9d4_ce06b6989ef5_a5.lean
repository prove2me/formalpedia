-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_bound__p2m_8c9b5a27_aa8a_47a8_b9d4_ce06b6989ef5_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:24:05.469477+00:00
-- url     : https://prove2.me/submissions/10ff8f75-a19c-43d1-ba16-40788a912da2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_data__p2m_abe9ada7_d03e_4dfe_be97_61dab793415e_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hConn : K.Connected)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_data__p2m_abe9ada7_d03e_4dfe_be97_61dab793415e_a1
      K hConn hK hCard
  omega