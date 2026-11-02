-- Prove2me | solution 1 for WilliamsonShmoys_euler_face_count_from_drawing__p2m_78e6a567_9e35_4430_95ce_28355556e16a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T20:17:14.157932+00:00
-- url     : https://prove2.me/submissions/82d3f9f1-7d8c-461c-917c-172bd5c74d4f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun f : Nat =>
      Int.ofNat (Fintype.card V) - Int.ofNat K.edgeSet.ncard + Int.ofNat f = 2 := by
  classical
  have hedge : Fintype.card ↑K.edgeSet = K.edgeSet.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hbound : Fintype.card V <= K.edgeSet.ncard + 1 := by
    calc
      Fintype.card V = Nat.card V := Nat.card_eq_fintype_card.symm
      _ <= Nat.card ↑K.edgeSet + 1 := hconn.card_vert_le_card_edgeSet_add_one
      _ = Fintype.card ↑K.edgeSet + 1 := by rw [Nat.card_eq_fintype_card]
      _ = K.edgeSet.ncard + 1 := by rw [hedge]
  let f : Nat := K.edgeSet.ncard + 2 - Fintype.card V
  refine Exists.intro f ?_
  dsimp [f]
  have hle : Fintype.card V <= K.edgeSet.ncard + 2 := by omega
  rw [Nat.cast_sub hle]
  push_cast
  omega