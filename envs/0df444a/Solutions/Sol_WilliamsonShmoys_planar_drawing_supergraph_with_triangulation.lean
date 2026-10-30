-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_supergraph_with_triangulation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:15:06.670269+00:00
-- url     : https://prove2.me/submissions/3de5141e-a352-4551-92bd-66e232a18646

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_exists
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_71ca74e3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hV : 3 ≤ Fintype.card V) :
    ∃ W : SimpleGraph V,
      LE.le Z W ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      3 * Fintype.card V - 6 = W.edgeSet.ncard := by
  obtain ⟨W, hZW, hW, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_exists Z hZ
  exact ⟨W, hZW, hW,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_71ca74e3 W hW hmax hV⟩