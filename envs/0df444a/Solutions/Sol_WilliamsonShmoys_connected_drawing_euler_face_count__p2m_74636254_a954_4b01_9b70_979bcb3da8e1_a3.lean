-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawing_euler_face_count__p2m_74636254_a954_4b01_9b70_979bcb3da8e1_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:34:33.598558+00:00
-- url     : https://prove2.me/submissions/82511072-6b7b-429f-8150-190a21a2a25b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    exists f : Nat,
      Fintype.card V + f = G.edgeSet.ncard + 2 := by
  have hconn_card : Nat.card V ≤ Nat.card G.edgeSet + 1 :=
    hconn.card_vert_le_card_edgeSet_add_one
  have hV : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  have hE : Nat.card G.edgeSet = G.edgeSet.ncard := by
    simp
  have hbound : Fintype.card V ≤ G.edgeSet.ncard + 1 := by
    omega
  refine ⟨G.edgeSet.ncard + 2 - Fintype.card V, ?_⟩
  omega