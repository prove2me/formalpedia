-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_same_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:08:00.936278+00:00
-- url     : https://prove2.me/submissions/48e74f34-c08a-446b-84e4-0c7f14a1d7a3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_exists_maximal_supergraph_repair
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_completion_repair

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ W : SimpleGraph V,
      Z ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧
        3 * Fintype.card V = W.edgeSet.ncard + 6 := by
  obtain ⟨W, hZW, hW, hmax⟩ :=
    WilliamsonShmoys.planar_completion_exists_maximal_supergraph_repair Z hZ
  exact ⟨W, hZW, hW,
    WilliamsonShmoys.edge_count_of_maximal_completion_repair W hV hW hmax⟩