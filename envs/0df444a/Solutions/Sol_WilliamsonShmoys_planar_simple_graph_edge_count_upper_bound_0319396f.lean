-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound_0319396f
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:24:26.451894+00:00
-- url     : https://prove2.me/submissions/d5c87c38-cf0d-4a78-b491-1fc90393e70e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_connected_component_partition
import Theorems.Thm_WilliamsonShmoys_planar_component_local_edge_estimate
import Theorems.Thm_WilliamsonShmoys_component_edge_count_aggregation
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨C, hNonempty, hUnique, hNoCross, hConnected, hDrawing⟩ :=
    WilliamsonShmoys.planar_connected_component_partition H hH
  have hPartition :
      (∀ S ∈ C, S.Nonempty) ∧
        ∀ v : V, ∃! S : Finset V, S ∈ C ∧ v ∈ S :=
    ⟨hNonempty, hUnique⟩
  have hLocal :=
    WilliamsonShmoys.planar_component_local_edge_estimate
      H C hPartition hConnected hDrawing
  exact WilliamsonShmoys.component_edge_count_aggregation
    H C hPartition hNoCross hLocal hV