-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_face_count__p2m_bddb7bfa_7c36_4521_ae23_809461c66ee9_a1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:15:31.770086+00:00
-- url     : https://prove2.me/submissions/c68283cd-eea1-4415-a4af-706716a4b3d9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by
  have h := (hconn).card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h
  exact ⟨G.edgeSet.ncard + 2 - Fintype.card V, by omega⟩
