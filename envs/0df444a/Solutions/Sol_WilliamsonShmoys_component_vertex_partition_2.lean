-- Prove2me | solution 2 for WilliamsonShmoys.component_vertex_partition
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T19:10:22.976037+00:00
-- url     : https://prove2.me/submissions/bbc1364e-db7d-410b-b12f-b9996c4c684d

import Mathlib
import Theorems.Thm_WilliamsonShmoys_component_blocks_nonempty
import Theorems.Thm_WilliamsonShmoys_component_blocks_disjoint
import Theorems.Thm_WilliamsonShmoys_component_blocks_cover
import Theorems.Thm_WilliamsonShmoys_component_blocks_contain_adjacent_vertices
import Theorems.Thm_WilliamsonShmoys_component_blocks_induced_connected
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    ∃ parts : Finset (Finset V),
      (∀ C ∈ parts, C.Nonempty) ∧
      (∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D) ∧
      parts.biUnion id = Finset.univ ∧
      (∀ u v, G.Adj u v → ∃ C ∈ parts, u ∈ C ∧ v ∈ C) ∧
      (∀ C ∈ parts, (G.induce (fun v => v ∈ C)).Connected) := by
  classical
  let parts : Finset (Finset V) :=
    Finset.univ.image (fun v : V => Finset.univ.filter (fun w : V => G.Reachable v w))
  refine ⟨parts, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [parts] using WilliamsonShmoys.component_blocks_nonempty G
  · simpa [parts] using WilliamsonShmoys.component_blocks_disjoint G
  · simpa [parts] using WilliamsonShmoys.component_blocks_cover G
  · simpa [parts] using WilliamsonShmoys.component_blocks_contain_adjacent_vertices G
  · simpa [parts] using WilliamsonShmoys.component_blocks_induced_connected G