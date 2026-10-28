-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_planar_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:30:54.496101+00:00
-- url     : https://prove2.me/submissions/20469e3a-88e8-49ee-ac46-8ce8c57c57e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_completion_edge_count_same_vertices

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hmax : ∀ Y : SimpleGraph V, Z ≤ Y →
      WilliamsonShmoys.HasPlanarDrawingOn Y → Y = Z) :
    3 * Fintype.card V = Z.edgeSet.ncard + 6 := by
  obtain ⟨T, hZT, hT, hcard⟩ :=
    WilliamsonShmoys.planar_drawingOn_completion_edge_count_same_vertices Z hV hZ
  have hEq : T = Z := hmax T hZT hT
  simpa [hEq] using hcard