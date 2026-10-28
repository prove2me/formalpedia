-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion_fixed_vertices_e7f6fb70
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:00:41.615902+00:00
-- url     : https://prove2.me/submissions/3f1d7df7-e431-46e6-bae2-ceb1a34f15dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_fixed_vertices_e7f6fb70_maximal_completion
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_fixed_vertices_e7f6fb70_maximal_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X) :
    Exists fun Y : SimpleGraph V =>
      X <= Y /\ WilliamsonShmoys.HasPlanarDrawingOn Y /\
      3 * Fintype.card V = Y.edgeSet.ncard + 6 := by
  obtain ⟨Y, hXY, hY, hmax⟩ :=
    WilliamsonShmoys.planar_triangulation_completion_fixed_vertices_e7f6fb70_maximal_completion
      X hV hX
  have hcount :=
    WilliamsonShmoys.planar_triangulation_completion_fixed_vertices_e7f6fb70_maximal_edge_count
      Y hV hY hmax
  exact ⟨Y, hXY, hY, hcount⟩
