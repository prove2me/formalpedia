-- Prove2me | solution 1 for SimpleGraphEdgeCardMonotone__p2m_cf08a975_8aa0_46e9_901e_a88c02c5eb25_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T19:11:19.473554+00:00
-- url     : https://prove2.me/submissions/5e82c691-41f7-4b8f-a611-659d10e88eea

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G K : SimpleGraph V)
    (h : ∀ u v, G.Adj u v → K.Adj u v) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : DecidableRel K.Adj := Classical.decRel K.Adj
     G.edgeFinset.card ≤ K.edgeFinset.card) ∧
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : DecidableRel K.Adj := Classical.decRel K.Adj
     (¬ (∀ u v, K.Adj u v → G.Adj u v) →
       G.edgeFinset.card < K.edgeFinset.card)) := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  constructor
  · exact Finset.card_le_card (SimpleGraph.edgeFinset_mono h)
  · intro hnot
    have hss : G.edgeFinset ⊂ K.edgeFinset := by
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · exact SimpleGraph.edgeFinset_mono h
      · intro heq
        have hsub : K.edgeFinset ⊆ G.edgeFinset := by
          simpa [heq]
        have hKG : K ≤ G :=
          (SimpleGraph.edgeFinset_subset_edgeFinset).mp hsub
        apply hnot
        intro u v huv
        exact hKG huv
    exact Finset.card_lt_card hss