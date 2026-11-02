-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_for_property__p2m_b05574a0_b431_4a4f_aba2_4718b07b1171_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:24:47.418175+00:00
-- url     : https://prove2.me/submissions/7834cd12-ff85-444f-ae3c-f38edf2e2787

import Mathlib

set_option autoImplicit false

open Finset

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hP : P H) :
    ∃ M : SimpleGraph V,
      H ≤ M ∧
      P M ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel M.Adj := Classical.decRel M.Adj
       H.edgeFinset.card ≤ M.edgeFinset.card) ∧
      (∀ N : SimpleGraph V, M ≤ N → P N → N ≤ M) := by
  classical
  let feasible : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => H ≤ G ∧ P G
  have hfeasible : feasible.Nonempty := by
    refine ⟨H, ?_⟩
    simp [feasible, hP]
  obtain ⟨M, hMmem, hMmax⟩ :=
    Finset.exists_max_image feasible (fun G => G.edgeFinset.card) hfeasible
  have hHM : H ≤ M := (Finset.mem_filter.mp hMmem).2.1
  have hPM : P M := (Finset.mem_filter.mp hMmem).2.2
  refine ⟨M, hHM, hPM, ?_, ?_⟩
  · letI : DecidableRel H.Adj := Classical.decRel H.Adj
    letI : DecidableRel M.Adj := Classical.decRel M.Adj
    exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hHM)
  · intro N hMN hPN
    by_contra hNM
    have hNmem : N ∈ feasible := by
      simp only [feasible, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨le_trans hHM hMN, hPN⟩
    have hne : M ≠ N := by
      intro heq
      apply hNM
      simpa [heq] using (le_rfl : M ≤ M)
    have hcard : M.edgeFinset.card < N.edgeFinset.card := by
      exact Finset.card_lt_card
        (SimpleGraph.edgeFinset_strict_mono (lt_of_le_of_ne hMN hne))
    exact (not_lt_of_ge (hMmax N hNmem)) hcard