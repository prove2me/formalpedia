-- Prove2me | solution 2 for WilliamsonShmoys.exists_planar_supergraph_with_triangulated_edge_count__p2m_ff88384e_13a7_4e55_8777_790088f23a4a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:23:56.132734+00:00
-- url     : https://prove2.me/submissions/834305f0-8163-4080-89ea-b913189fe82f

import Theorems.Thm_WilliamsonShmoys_exists_planar_edge_count_extension_54a0e51c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.exists_planar_edge_count_extension_54a0e51c L hL hcard
