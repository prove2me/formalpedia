-- Prove2me | solution 1 for WilliamsonShmoys.connected_edge_lower_bound__p2m_961b854d_f4cc_4b36_ad05_39668b153494_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:57:17.632271+00:00
-- url     : https://prove2.me/submissions/5e92dbfc-161d-45ec-94d8-44cb316b5a0a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hconn : K.Connected) :
    Fintype.card V ≤ K.edgeFinset.card + 1 := by
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  rw [Nat.card_eq_fintype_card] at h
  rw [← SimpleGraph.edgeFinset_card] at h
  exact h