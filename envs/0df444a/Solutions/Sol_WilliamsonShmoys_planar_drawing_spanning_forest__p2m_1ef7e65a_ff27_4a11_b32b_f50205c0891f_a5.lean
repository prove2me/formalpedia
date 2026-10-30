-- Prove2me | solution 1 for WilliamsonShmoys_planar_drawing_spanning_forest__p2m_1ef7e65a_ff27_4a11_b32b_f50205c0891f_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:05:25.482655+00:00
-- url     : https://prove2.me/submissions/53efbb87-68fb-4e55-8ece-0e59849611ed

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Theorems.Thm_finiteAcyclicSubgraph_edge_count_components__p2m_50f5601b_e154_4acb_9deb_d7586c738d35_a3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    ∃ H : SimpleGraph V,
      (∀ u v, H.Adj u v → G.Adj u v) ∧
      H.IsAcyclic ∧
      (∀ u v, G.Reachable u v → H.Reachable u v) ∧
      H.edgeSet.ncard + Nat.card G.ConnectedComponent = Fintype.card V := by
  classical
  obtain ⟨H, hHG, hAcyclic, hReach⟩ := G.exists_isAcyclic_reachable_eq_le
  refine ⟨H, ?_, hAcyclic, ?_, ?_⟩
  · intro u v huv
    exact hHG huv
  · intro u v huv
    rw [hReach]
    exact huv
  · exact finiteAcyclicSubgraph_edge_count_components__p2m_50f5601b_e154_4acb_9deb_d7586c738d35_a3
      H G hAcyclic (by
        intro u v
        rw [hReach])