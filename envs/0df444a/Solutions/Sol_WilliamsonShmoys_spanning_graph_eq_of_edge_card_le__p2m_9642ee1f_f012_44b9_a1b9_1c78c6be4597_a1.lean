-- Prove2me | solution 1 for WilliamsonShmoys.spanning_graph_eq_of_edge_card_le__p2m_9642ee1f_f012_44b9_a1b9_1c78c6be4597_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:16:39.137044+00:00
-- url     : https://prove2.me/submissions/df6e3da6-a066-4de1-998a-30dcf2812e15

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (G K : SimpleGraph V)
    (hGK : ∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v)
    (hcard : (letI : DecidableRel G.Adj := Classical.decRel G.Adj
      letI : DecidableRel K.Adj := Classical.decRel K.Adj
      K.edgeFinset.card ≤ G.edgeFinset.card)) : K = G := by
  classical
  have hsubset : G.edgeFinset ⊆ K.edgeFinset :=
    SimpleGraph.edgeFinset_subset_edgeFinset.mpr hGK
  have hcard' : K.edgeFinset.card ≤ G.edgeFinset.card := by
    simpa using hcard
  have hedge : G.edgeFinset = K.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsubset hcard'
  exact SimpleGraph.edgeFinset_inj.mp hedge.symm