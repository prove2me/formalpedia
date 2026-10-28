-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_bound_triangulation_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:12:16.222442+00:00
-- url     : https://prove2.me/submissions/b501b0f1-a697-4cce-9960-c8639bd5c6a2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_planar_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_planar_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ Z : SimpleGraph V, W ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      3 * Fintype.card V = Z.edgeSet.ncard + 6 := by
  obtain ⟨Z, hWZ, hZ, hmax⟩ :=
    WilliamsonShmoys.drawable_planar_maximal_supergraph W hW
  exact ⟨Z, hWZ, hZ,
    WilliamsonShmoys.maximal_drawable_planar_edge_count Z hV hZ hmax⟩