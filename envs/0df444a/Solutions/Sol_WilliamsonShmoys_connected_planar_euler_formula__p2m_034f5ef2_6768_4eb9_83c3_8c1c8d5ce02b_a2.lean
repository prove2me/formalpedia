-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_euler_formula__p2m_034f5ef2_6768_4eb9_83c3_8c1c8d5ce02b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:55:12.731643+00:00
-- url     : https://prove2.me/submissions/8e4ca8e5-5499-421e-a9df-90d6bc76d4c8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeFinset.card + 2 := by
  have hle : Fintype.card V ≤ H.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using
      hconn.card_vert_le_card_edgeSet_add_one
  refine ⟨H.edgeFinset.card + 2 - Fintype.card V, ?_⟩
  omega