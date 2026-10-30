-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_density_topology_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:02:55.598924+00:00
-- url     : https://prove2.me/submissions/68a5e6a2-b160-4296-ae0d-c748659e5a7b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_augmentation_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ H.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by
  obtain ⟨K, hHK, hK, hbound⟩ :=
    WilliamsonShmoys.maximal_planar_graph_augmentation_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c
      H hH hV
  have hKH : K.edgeSet ⊆ H.edgeSet := hmax K hHK hK
  have heq : H.edgeSet = K.edgeSet := Set.Subset.antisymm hHK hKH
  simpa [heq] using hbound