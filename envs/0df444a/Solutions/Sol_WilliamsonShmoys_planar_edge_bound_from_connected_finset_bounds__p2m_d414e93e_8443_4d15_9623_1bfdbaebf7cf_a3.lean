-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_from_connected_finset_bounds__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:27:37.529035+00:00
-- url     : https://prove2.me/submissions/1e2520cf-5378-4ddb-91d1-2c0806fd3116

import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_component_partition_data__p2m_2aff762d_92be_4091_96b6_7b0d6e06700b_a1
import Theorems.Thm_WilliamsonShmoys_sum_component_edge_bound__p2m_2aff762d_92be_4091_96b6_7b0d6e06700b_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hcomponents : ∀ (W : Finset V), 3 ≤ W.card →
      (M.induce (W : Set V)).Connected →
      (M.induce (W : Set V)).edgeSet.ncard + 6 ≤ 3 * W.card) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨parts, _hpartition, hcard, hedges, hconn, hsmall⟩ :=
    WilliamsonShmoys.connected_component_partition_data__p2m_2aff762d_92be_4091_96b6_7b0d6e06700b_a1 M
  exact WilliamsonShmoys.sum_component_edge_bound__p2m_2aff762d_92be_4091_96b6_7b0d6e06700b_a1
    M hV hcomponents parts hcard hedges hconn hsmall