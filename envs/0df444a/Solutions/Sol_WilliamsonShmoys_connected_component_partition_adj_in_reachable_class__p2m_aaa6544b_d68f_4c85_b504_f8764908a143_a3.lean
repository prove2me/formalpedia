-- Prove2me | solution 1 for WilliamsonShmoys.connected_component_partition_adj_in_reachable_class__p2m_aaa6544b_d68f_4c85_b504_f8764908a143_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:44:35.246923+00:00
-- url     : https://prove2.me/submissions/98196df7-4b1e-4704-94b8-b5446cd8c481

import Mathlib
open Classical
open SimpleGraph

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) {u v : V}
    (h : M.Adj u v) : v ∈ Finset.univ.filter (fun w => M.Reachable u w) := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Adj.reachable h⟩