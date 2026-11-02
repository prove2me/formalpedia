-- Prove2me | solution 1 for WilliamsonShmoys.supergraph_edge_count_completion__p2m_de823218_b35b_47b7_9852_26ba1b994051_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:38:55.609436+00:00
-- url     : https://prove2.me/submissions/0ef6b3fb-c532-4334-a8d0-f732817c1549

import Mathlib
import Theorems.Thm_WilliamsonShmoys_simple_graph_edge_count_completion__p2m_3be8fb19_1696_42e0_add6_8cf83fd59ba5_a2
import Theorems.Thm_WilliamsonShmoys_three_n_sub_six_le_choose_two__p2m_3be8fb19_1696_42e0_add6_8cf83fd59ba5_a2

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hbound : letI : DecidableRel G.Adj := Classical.decRel G.Adj
      G.edgeFinset.card ≤ 3 * Fintype.card V - 6) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       Fintype.card V - 2 ≤ H.edgeFinset.card ∧
       H.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  classical
  let n := Fintype.card V
  let m := max (n - 2) G.edgeFinset.card
  have hG : G.edgeFinset.card ≤ 3 * n - 6 := by
    simpa [n] using hbound
  have hlow : n - 2 ≤ 3 * n - 6 := by omega
  have hm : m ≤ 3 * n - 6 := max_le hlow hG
  have hcap : m ≤ Nat.choose n 2 :=
    le_trans hm (WilliamsonShmoys.three_n_sub_six_le_choose_two__p2m_3be8fb19_1696_42e0_add6_8cf83fd59ba5_a2 n hcard)
  obtain ⟨H, hGH, hHcard⟩ :=
    WilliamsonShmoys.simple_graph_edge_count_completion__p2m_3be8fb19_1696_42e0_add6_8cf83fd59ba5_a2
      G m (le_max_right (n - 2) G.edgeFinset.card) hcap
  refine ⟨H, hGH, ?_, ?_⟩
  · have hlow' : n - 2 ≤ m := le_max_left (n - 2) G.edgeFinset.card
    rw [hHcard]
    change n - 2 ≤ m
    exact hlow'
  · simpa [n, hHcard] using hm