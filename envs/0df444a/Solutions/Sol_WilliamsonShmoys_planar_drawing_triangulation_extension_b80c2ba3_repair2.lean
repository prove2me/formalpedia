-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_b80c2ba3_repair2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:29:10.566596+00:00
-- url     : https://prove2.me/submissions/21794004-f242-446a-a1b8-a5f7153abce6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_b80c2ba3_repair2_exists_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_b80c2ba3_repair2_maximal_graph_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet ⊆ N.edgeSet ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hN, hMN, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_b80c2ba3_repair2_exists_maximal_supergraph
      M hDrawing
  refine ⟨N, hN, hMN, ?_⟩
  exact WilliamsonShmoys.planar_drawing_triangulation_extension_b80c2ba3_repair2_maximal_graph_edge_count
    N hCard hN hmax