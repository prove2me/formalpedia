-- Prove2me | solution 1 for WilliamsonShmoys.simple_graph_small_edge_bound__p2m_8e79e615_ce68_4197_8611_7fa93173a04e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:31:19.761249+00:00
-- url     : https://prove2.me/submissions/4061645b-3d79-46ed-aa5d-c6422ab4dfc3

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hsmall : Fintype.card V < 3) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     K.edgeFinset.card ≤ 1) := by
  classical
  have hbound : K.edgeFinset.card ≤ (Fintype.card V).choose 2 :=
    K.card_edgeFinset_le_card_choose_two
  let n := Fintype.card V
  have hn : n ≤ 2 := by
    dsimp [n]
    omega
  have hchoose : n.choose 2 ≤ 1 := by
    interval_cases n <;> norm_num at hn ⊢
  simpa [n] using hbound.trans hchoose