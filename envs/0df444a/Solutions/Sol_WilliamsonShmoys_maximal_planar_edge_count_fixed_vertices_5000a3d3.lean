-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_fixed_vertices_5000a3d3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:37:31.008887+00:00
-- url     : https://prove2.me/submissions/0dd02c96-af53-4328-8fd5-5576d88ca773
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_fixed_vertices_e7f6fb70

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hmax : ∀ Y : SimpleGraph V,
      X ≤ Y → WilliamsonShmoys.HasPlanarDrawingOn Y → Y ≤ X) :
    3 * Fintype.card V = X.edgeSet.ncard + 6 := by
  obtain ⟨Y, hXY, hY, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_completion_fixed_vertices_e7f6fb70 X hV hX
  have hYX : Y ≤ X := hmax Y hXY hY
  have hEq : Y = X := le_antisymm hYX hXY
  simpa [hEq] using hcount