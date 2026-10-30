-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion_fixed_vertices_e7f6fb70_maximal_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:27:05.0773+00:00
-- url     : https://prove2.me/submissions/a17c8034-d532-4289-90c4-6d2ad1c38d84

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_e7f6fb70
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_lower_bound_e7f6fb70

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hmax : forall Z : SimpleGraph V, Y <= Z ->
      WilliamsonShmoys.HasPlanarDrawingOn Z -> Z = Y) :
    3 * Fintype.card V = Y.edgeSet.ncard + 6 := by
  have hup := WilliamsonShmoys.planar_drawing_edge_upper_bound_e7f6fb70 Y hV hY
  have hlo := WilliamsonShmoys.maximal_drawing_edge_lower_bound_e7f6fb70 Y hV hY hmax
  omega