-- Prove2me | solution 1 for WilliamsonShmoys.connected_induced_planar_edge_count_upper__p2m_30d6faec_b0bf_4bef_98dc_af9f33dfa7ee_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:37:35.675192+00:00
-- url     : https://prove2.me/submissions/2abd947b-7f26-46b1-bd5e-40ba743dce99

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_connected_induced__p2m_66ade5d4_3842_4532_bbd5_36e43a15d1f5_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (s : Finset V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ s.card)
    (hconn : (H.induce (↑s : Set V)).Connected) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    (H.induce (↑s : Set V)).edgeFinset.card ≤ 3 * s.card - 6 := by
  classical
  have hc : 3 ≤ Fintype.card {v // v ∈ s} := by simpa using hcard
  have hb := WilliamsonShmoys.planar_edge_bound_connected_induced__p2m_66ade5d4_3842_4532_bbd5_36e43a15d1f5_a1 H hdraw s hconn hc
  have hb' : (H.induce (↑s : Set V)).edgeSet.ncard + 6 ≤ 3 * s.card := by
    simpa only [Fintype.card_coe] using hb
  rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]
  omega
