-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_certificate__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:27:51.330137+00:00
-- url     : https://prove2.me/submissions/41358051-3cc8-4bc6-8de3-5a13f272343c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_count__p2m_bddb7bfa_7c36_4521_ae23_809461c66ee9_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_bddb7bfa_7c36_4521_ae23_809461c66ee9_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by
  obtain ⟨f, hf⟩ :=
    WilliamsonShmoys.connected_planar_drawing_euler_face_count__p2m_bddb7bfa_7c36_4521_ae23_809461c66ee9_a1
      G hconn hdraw
  have hedge :=
    WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_bddb7bfa_7c36_4521_ae23_809461c66ee9_a1
      G hconn hdraw hCard
  exact ⟨f, hf, by nlinarith⟩