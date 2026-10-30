-- Prove2me | solution 1 for component_edge_partition_sum__p2m_cd99b0ce_6168_4c6b_a6a6_0ae22062f109_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:26:35.3889+00:00
-- url     : https://prove2.me/submissions/1375889f-2dff-447b-bf1c-032b0fdc7250

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Set.Card
import Theorems.Thm_component_edge_partition_count__p2m_18b4f874_2377_4148_8ba5_149b9ea6fe45_a1

open SimpleGraph

theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) [Fintype G.ConnectedComponent] :
    G.edgeSet.ncard + Nat.card G.ConnectedComponent =
      Finset.univ.sum (fun C : G.ConnectedComponent => C.toSimpleGraph.edgeSet.ncard + 1) := by
  rw [Finset.sum_add_distrib]
  rw [component_edge_partition_count__p2m_18b4f874_2377_4148_8ba5_149b9ea6fe45_a1]
  simp