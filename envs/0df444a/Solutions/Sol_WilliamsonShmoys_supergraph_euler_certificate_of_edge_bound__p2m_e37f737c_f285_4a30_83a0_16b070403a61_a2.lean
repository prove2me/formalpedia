-- Prove2me | solution 1 for WilliamsonShmoys.supergraph_euler_certificate_of_edge_bound__p2m_e37f737c_f285_4a30_83a0_16b070403a61_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:02:38.092279+00:00
-- url     : https://prove2.me/submissions/d1303c68-2eb2-4813-9cc3-391b4c4b40c6

import Mathlib
import Theorems.Thm_WilliamsonShmoys_supergraph_edge_count_completion__p2m_de823218_b35b_47b7_9852_26ba1b994051_a2
import Theorems.Thm_WilliamsonShmoys_euler_certificate_of_edge_interval__p2m_de823218_b35b_47b7_9852_26ba1b994051_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hbound : letI : DecidableRel G.Adj := Classical.decRel G.Adj
      G.edgeFinset.card ≤ 3 * Fintype.card V - 6) :
    ∃ (H : SimpleGraph V) (f : ℕ),
      G ≤ H ∧
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       G.edgeFinset.card ≤ H.edgeFinset.card) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       Fintype.card V + f = H.edgeFinset.card + 2) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       3 * f ≤ 2 * H.edgeFinset.card) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  obtain ⟨H, hGH, hlow, hup⟩ :=
    WilliamsonShmoys.supergraph_edge_count_completion__p2m_de823218_b35b_47b7_9852_26ba1b994051_a2
      G hcard (by simpa using hbound)
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  obtain ⟨f, heq, hineq⟩ :=
    WilliamsonShmoys.euler_certificate_of_edge_interval__p2m_de823218_b35b_47b7_9852_26ba1b994051_a2
      (Fintype.card V) H.edgeFinset.card hcard hlow hup
  refine ⟨H, f, hGH, ?_, heq, hineq⟩
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)