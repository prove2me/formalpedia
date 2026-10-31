-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_equation__p2m_62a3a1a3_c41c_45ae_9d73_85a6165d1dd4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:39:56.547646+00:00
-- url     : https://prove2.me/submissions/92e4385f-abd6-433a-a219-48f4e90b050a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by
  have hconn_card := hconn.card_vert_le_card_edgeSet_add_one
  have hle : Fintype.card V ≤ G.edgeSet.ncard + 1 := by
    simpa only [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hconn_card
  refine ⟨G.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega