-- Prove2me | solution 1 for WilliamsonShmoys.induced_edges_zero_of_card_le_one__p2m_66d9a9d7_c76c_45c0_887d_01a07c3b39fb_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:14:49.7952+00:00
-- url     : https://prove2.me/submissions/5d193ac6-264f-45cd-88ea-97642299e0d8

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (s : Finset V) (hs : Fintype.card s ≤ 1) :
    (letI : DecidableRel (K.induce (↑s : Set V)).Adj := Classical.decRel _;
      (K.induce (↑s : Set V)).edgeFinset.card = 0) := by
  classical
  have hcard : Fintype.card (↑s : Type _) ≤ 1 := hs
  have hbound := SimpleGraph.card_edgeFinset_le_card_choose_two
    (G := K.induce (↑s : Set V))
  have hlt : Fintype.card (↑s : Type _) < 2 := by omega
  have hchoose : (Fintype.card (↑s : Type _)).choose 2 = 0 :=
    Nat.choose_eq_zero_of_lt hlt
  have hbound' : (K.induce (↑s : Set V)).edgeFinset.card ≤
      (Fintype.card (↑s : Type _)).choose 2 := by
    simpa using hbound
  change (K.induce (↑s : Set V)).edgeFinset.card = 0
  rw [hchoose] at hbound'
  omega