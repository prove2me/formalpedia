-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_orderedEdgeCount_facts__p2m_bf9a75f5_fb19_4298_9037_82dd49bb2208_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-10T17:11:08.033827+00:00
-- url     : https://prove2.me/submissions/3104b30f-bae2-42e4-9f5d-250e937252f6

import Mathlib

open scoped BigOperators

set_option autoImplicit false

/-- Ordered adjacent pairs: the total count is bounded by `|V × V|`, and a strictly larger graph has
strictly more ordered adjacent pairs. -/
theorem solution {V : Type*} [Fintype V] (H H' : SimpleGraph V) [DecidableRel H.Adj]
    [DecidableRel H'.Adj] :
    (∀ (K : SimpleGraph V) [DecidableRel K.Adj],
        Fintype.card {p : V × V // K.Adj p.1 p.2} ≤ Fintype.card (V × V)) ∧
      (H < H' →
        Fintype.card {p : V × V // H.Adj p.1 p.2} <
          Fintype.card {p : V × V // H'.Adj p.1 p.2}) := by
  classical
  have hcard : ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card {p : V × V // G.Adj p.1 p.2} = 2 * G.edgeFinset.card := by
    intro G _
    rw [Fintype.card_subtype, ← SimpleGraph.two_mul_card_edgeFinset]
  constructor
  · intro K _
    exact Fintype.card_subtype_le _
  · intro hlt
    rw [hcard H, hcard H']
    have hle : H ≤ H' := le_of_lt hlt
    have hnot : ¬ H' ≤ H := not_le_of_gt hlt
    have hex : ∃ u v, H'.Adj u v ∧ ¬ H.Adj u v := by
      by_contra h
      apply hnot
      intro u v huv
      by_contra h2
      exact h ⟨u, v, huv, h2⟩
    obtain ⟨u, v, huv', huv⟩ := hex
    have hsub : H.edgeFinset ⊆ H'.edgeFinset := SimpleGraph.edgeFinset_mono hle
    have hssub : H.edgeFinset ⊂ H'.edgeFinset := by
      rw [Finset.ssubset_iff_of_subset hsub]
      refine ⟨s(u, v), ?_, ?_⟩
      · rw [SimpleGraph.mem_edgeFinset]
        exact (SimpleGraph.mem_edgeSet H').mpr huv'
      · rw [SimpleGraph.mem_edgeFinset]
        exact fun h => huv ((SimpleGraph.mem_edgeSet H).mp h)
    have hlt2 : H.edgeFinset.card < H'.edgeFinset.card := Finset.card_lt_card hssub
    omega
