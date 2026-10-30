-- Prove2me | solution 1 for component_edge_partition_count__p2m_18b4f874_2377_4148_8ba5_149b9ea6fe45_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:21:28.244803+00:00
-- url     : https://prove2.me/submissions/093574e2-82b5-4f1f-9a0f-618c2d68f746

import Theorems.Thm_component_edge_type_equiv__p2m_ad62d6f2_3818_4a29_8c23_e55e80cb22b1_a1

open SimpleGraph

theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) [Fintype G.ConnectedComponent] :
    G.edgeSet.ncard = Finset.univ.sum (fun C : G.ConnectedComponent => C.toSimpleGraph.edgeSet.ncard) := by
  classical
  simpa only [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_sigma] using
    Nat.card_congr
      (Classical.choice (component_edge_type_equiv__p2m_ad62d6f2_3818_4a29_8c23_e55e80cb22b1_a1 G))