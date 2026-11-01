-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_certificate__p2m_3061538d_e777_4f56_997f_0c12065c9e75_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:32:57.742936+00:00
-- url     : https://prove2.me/submissions/7168ad62-6ef2-4e02-8684-8246eaf85e74

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_abda76d0_f206_4b5c_973f_e20fb605b671_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_length_bound__p2m_abda76d0_f206_4b5c_973f_e20fb605b671_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 <= Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f <= 2 * G.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ := WilliamsonShmoys.planar_drawing_euler_face_count__p2m_abda76d0_f206_4b5c_973f_e20fb605b671_a1
    G hplanar hconn hcard
  exact ⟨f, hEuler,
    WilliamsonShmoys.planar_drawing_face_length_bound__p2m_abda76d0_f206_4b5c_973f_e20fb605b671_a1
      G hplanar hconn hcard f hEuler⟩