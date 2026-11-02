-- Prove2me | solution 1 for WilliamsonShmoys.SimpleGraph.edge_card_mono_and_eq_of_le__p2m_8bdcd24b_0a33_4788_8eda_5b06fcc2996a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:37:35.662994+00:00
-- url     : https://prove2.me/submissions/38f9e993-bc82-4ad4-a4fa-6c8dcc514c18

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hGH : G ≤ H) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : DecidableRel H.Adj := Classical.decRel H.Adj
     G.edgeFinset.card ≤ H.edgeFinset.card ∧
       (H.edgeFinset.card ≤ G.edgeFinset.card → G = H)) := by
  classical
  constructor
  · exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hGH)
  · intro hcard
    apply SimpleGraph.edgeFinset_inj.mp
    exact Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hGH) hcard