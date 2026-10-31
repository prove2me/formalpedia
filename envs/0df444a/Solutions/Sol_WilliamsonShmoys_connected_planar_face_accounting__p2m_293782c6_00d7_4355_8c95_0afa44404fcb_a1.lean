-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_face_accounting__p2m_293782c6_00d7_4355_8c95_0afa44404fcb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:40:01.600013+00:00
-- url     : https://prove2.me/submissions/de332147-06ad-41a6-bb39-e0334de67c87

import Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_face_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hconn : G.Connected) (hV : 3 ≤ Fintype.card V) : ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 ∧ 3 * f ≤ 2 * G.edgeSet.ncard :=
  WilliamsonShmoys.connected_drawing_euler_face_bound G hG hconn hV
