-- Prove2me | solution 1 for WilliamsonShmoys.edgeFinset_card_le_edgeSet_ncard_of_subset__p2m_a34ee183_b91b_4a67_873f_251f94ba9522_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:23:07.410085+00:00
-- url     : https://prove2.me/submissions/e875a739-f6bc-438b-9113-9788016c5017

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V) [DecidableRel K.Adj]
    (hKH : K.edgeSet ⊆ H.edgeSet) :
    K.edgeFinset.card ≤ H.edgeSet.ncard := by
  classical
  have hfin : K.edgeFinset ⊆ H.edgeFinset := by
    intro e he
    simp only [SimpleGraph.mem_edgeFinset] at he ⊢
    exact hKH he
  calc
    K.edgeFinset.card ≤ H.edgeFinset.card := Finset.card_le_card hfin
    _ = Fintype.card H.edgeSet := H.edgeFinset_card
    _ = H.edgeSet.ncard := Set.fintypeCard_eq_ncard H.edgeSet