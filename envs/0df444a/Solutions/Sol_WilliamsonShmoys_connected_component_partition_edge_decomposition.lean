-- Prove2me | solution 1 for WilliamsonShmoys.connected_component_partition_edge_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:45:05.480179+00:00
-- url     : https://prove2.me/submissions/9a7c21d8-d505-48be-a8c8-afcf65b857d3

import Mathlib
import Theorems.Thm_WilliamsonShmoys_component_vertex_partition
import Theorems.Thm_WilliamsonShmoys_partition_edge_count

set_option autoImplicit false

open Finset

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    ∃ parts : Finset (Finset V),
      (∀ C ∈ parts, C.Nonempty) ∧
      (∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D) ∧
      parts.biUnion id = Finset.univ ∧
      G.edgeSet.ncard = ∑ C ∈ parts, (G.induce (fun v => v ∈ C)).edgeSet.ncard ∧
      (∀ C ∈ parts, (G.induce (fun v => v ∈ C)).Connected) := by
  obtain ⟨parts, hnonempty, hdisjoint, hcover, hadj, hconnected⟩ :=
    WilliamsonShmoys.component_vertex_partition G
  have hedgecount := WilliamsonShmoys.partition_edge_count G parts hdisjoint hcover hadj
  exact ⟨parts, hnonempty, hdisjoint, hcover, hedgecount, hconnected⟩