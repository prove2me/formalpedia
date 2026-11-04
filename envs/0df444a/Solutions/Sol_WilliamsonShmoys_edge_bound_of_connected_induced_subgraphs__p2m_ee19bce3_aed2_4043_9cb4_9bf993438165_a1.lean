-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_of_connected_induced_subgraphs__p2m_ee19bce3_aed2_4043_9cb4_9bf993438165_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:34:53.730664+00:00
-- url     : https://prove2.me/submissions/4cc7497f-3b16-462f-8144-0d76eac6ceb1

import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_connected_finset_bounds__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hconnBound : ∀ (s : Finset V), 3 ≤ s.card →
      (G.induce (↑s : Set V)).Connected →
      (letI : DecidableRel (G.induce (↑s : Set V)).Adj :=
        Classical.decRel (G.induce (↑s : Set V)).Adj
       (G.induce (↑s : Set V)).edgeFinset.card ≤
         3 * Fintype.card (↑(s : Set V)) - 6)) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  classical
  have hcomponents : ∀ (s : Finset V), 3 ≤ s.card →
      (G.induce (s : Set V)).Connected →
      (G.induce (s : Set V)).edgeSet.ncard + 6 ≤ 3 * s.card := by
    intro s hs hc
    letI : DecidableRel (G.induce (s : Set V)).Adj :=
      Classical.decRel (G.induce (s : Set V)).Adj
    have h := hconnBound s hs hc
    change (G.induce (s : Set V)).edgeFinset.card ≤
      3 * Fintype.card (↑(s : Set V)) - 6 at h
    have he : (G.induce (s : Set V)).edgeSet.ncard =
        (G.induce (s : Set V)).edgeFinset.card := by
      rw [← Set.fintypeCard_eq_ncard, ← SimpleGraph.edgeFinset_card]
    have hv : Fintype.card (↑(s : Set V)) = s.card := Fintype.card_coe s
    rw [hv] at h
    rw [he]
    omega
  have h :=
    WilliamsonShmoys.planar_edge_bound_from_connected_finset_bounds__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
      G hV hcomponents
  have he : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← Set.fintypeCard_eq_ncard, ← SimpleGraph.edgeFinset_card]
  rw [he] at h
  omega
