-- Prove2me | solution 1 for WilliamsonShmoys.small_card_complete_graph_edge_count__p2m_6ce4ca43_3f24_470a_9f5f_602e4f1a05ae_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:08:23.442504+00:00
-- url     : https://prove2.me/submissions/15c4fa69-5f59-48d9-a7d7-a7e2acb61fbf

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    [DecidableRel (⊤ : SimpleGraph V).Adj]
    (hsmall : Fintype.card V < 3) :
    (⊤ : SimpleGraph V).edgeFinset.card = (Fintype.card V).choose 2 := by
  let s : Finset (Sym2 V) := (⊤ : SimpleGraph V).edgeFinset
  change s.card = (Fintype.card V).choose 2
  letI : DecidableRel (⊤ : SimpleGraph V).Adj := SimpleGraph.Top.adjDecidable V
  have hs : s = (⊤ : SimpleGraph V).edgeFinset := by
    ext e
    simp [s, SimpleGraph.edgeFinset]
  rw [hs]
  exact SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := V)