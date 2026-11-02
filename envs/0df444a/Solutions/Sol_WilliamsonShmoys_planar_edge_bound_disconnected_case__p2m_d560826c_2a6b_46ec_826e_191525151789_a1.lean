-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_disconnected_case__p2m_d560826c_2a6b_46ec_826e_191525151789_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:16:08.819707+00:00
-- url     : https://prove2.me/submissions/0589346a-39af-40d7-b390-e59fdc0ba9ea

import Mathlib
import Theorems.Thm_WilliamsonShmoys_component_partition_and_edges__p2m_f78b2624_2de8_40ad_9230_053c73815f63_a3
import Theorems.Thm_WilliamsonShmoys_component_bounds_sum__p2m_f78b2624_2de8_40ad_9230_053c73815f63_a3
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hcard : 3 <= Fintype.card V)
    (hlocal : ∀ s : Finset V, 3 <= s.card →
      (N.induce (s : Set V)).Connected →
      (N.induce (s : Set V)).edgeFinset.card <= 3 * s.card - 6)
    (hdisconn : ¬ N.Connected) :
    N.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  letI : DecidableRel N.Adj := dN
  obtain ⟨ C, hnonempty, hpartition, hconnected, hedges ⟩ :=
    WilliamsonShmoys.component_partition_and_edges__p2m_f78b2624_2de8_40ad_9230_053c73815f63_a3 N dN
  exact WilliamsonShmoys.component_bounds_sum__p2m_f78b2624_2de8_40ad_9230_053c73815f63_a3
    N dN C hcard hpartition hnonempty hconnected hedges hlocal