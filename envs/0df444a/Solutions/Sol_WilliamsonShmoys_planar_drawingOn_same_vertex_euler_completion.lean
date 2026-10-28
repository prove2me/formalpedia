-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_same_vertex_euler_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:51:42.070748+00:00
-- url     : https://prove2.me/submissions/107c8a8e-ec63-47f6-a90e-bfd3d0db2011
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_supergraph_repair_3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_repair_3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet ⊆ N.edgeSet ∧
      3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  obtain ⟨N, hN, hMN, hNmax⟩ :=
    WilliamsonShmoys.planar_drawingOn_maximal_supergraph_repair_3 M hM hV
  exact ⟨N, hN, hMN,
    WilliamsonShmoys.maximal_planar_drawingOn_edge_count_repair_3 N
      ⟨hN, hNmax⟩ hV⟩