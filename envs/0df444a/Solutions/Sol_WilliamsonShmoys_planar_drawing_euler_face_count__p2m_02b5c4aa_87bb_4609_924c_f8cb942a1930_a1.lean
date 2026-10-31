-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_face_count__p2m_02b5c4aa_87bb_4609_924c_f8cb942a1930_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:11:30.225833+00:00
-- url     : https://prove2.me/submissions/7f77c8f9-3858-42af-827e-96f7c43da653

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by
  have hconn_card := hconn.card_vert_le_card_edgeSet_add_one
  have hle : Fintype.card V ≤ G.edgeSet.ncard + 1 := by
    simpa only [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hconn_card
  refine ⟨G.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega