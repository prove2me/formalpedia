-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:36:39.527367+00:00
-- url     : https://prove2.me/submissions/07c298c4-9e42-4692-aee9-d006408032aa

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_certificate__p2m_cfd012c7_8a6d_483e_9797_29a733a7d0a7_a1
import Theorems.Thm_WilliamsonShmoys_planar_face_count_arithmetic_bound__p2m_cfd012c7_8a6d_483e_9797_29a733a7d0a7_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hconn : T.Connected) : T.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨f, heuler, hinc⟩ :=
    WilliamsonShmoys.planar_drawing_face_count_certificate__p2m_cfd012c7_8a6d_483e_9797_29a733a7d0a7_a1
      T hV hT hconn
  exact WilliamsonShmoys.planar_face_count_arithmetic_bound__p2m_cfd012c7_8a6d_483e_9797_29a733a7d0a7_a1
    (Fintype.card V) T.edgeSet.ncard hV f heuler hinc