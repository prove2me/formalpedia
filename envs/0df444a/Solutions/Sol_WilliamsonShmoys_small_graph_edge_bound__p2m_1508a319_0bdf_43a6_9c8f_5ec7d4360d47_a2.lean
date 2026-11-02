-- Prove2me | solution 1 for WilliamsonShmoys.small_graph_edge_bound__p2m_1508a319_0bdf_43a6_9c8f_5ec7d4360d47_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:48:16.965142+00:00
-- url     : https://prove2.me/submissions/92990181-4507-488b-b19b-0620f668755b

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hn : Fintype.card V < 3) :
    letI : DecidableRel G.Adj := Classical.decRel _
    G.edgeFinset.card ≤ 3 * Fintype.card V - 3 := by
  classical
  have hE : G.edgeFinset.card ≤ (Fintype.card V).choose 2 :=
    SimpleGraph.card_edgeFinset_le_card_choose_two
  have hcases : Fintype.card V = 0 ∨ Fintype.card V = 1 ∨ Fintype.card V = 2 := by
    omega
  rcases hcases with h0 | h1 | h2
  · rw [h0] at hE ⊢
    norm_num at hE ⊢
    omega
  · rw [h1] at hE ⊢
    norm_num at hE ⊢
    omega
  · rw [h2] at hE ⊢
    norm_num at hE ⊢
    omega