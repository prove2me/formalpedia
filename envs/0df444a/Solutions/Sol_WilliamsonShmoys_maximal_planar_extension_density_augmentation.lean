-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension_density_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:55:56.48896+00:00
-- url     : https://prove2.me/submissions/52b8d47d-fe12-49c8-9720-ba54d85a7869
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_finite_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_density_topology_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      L.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by
  obtain ⟨H, hLH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_finite_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c
      L hL
  exact ⟨H, hLH, hH,
    WilliamsonShmoys.maximal_planar_graph_edge_density_topology_v2_3edeea81_4678_4d7e_9156_ecaccaea0c7c
      H hH hmax hV⟩
