-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_maximal_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T10:15:33.963417+00:00
-- url     : https://prove2.me/submissions/e4438fd8-79bd-4c35-bf10-6fe2f657db36
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_upper_bound_euler_exact_arcs
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_lower_bound_exact_arcs

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T) :
    3 * Fintype.card V = T.edgeSet.ncard + 6 := by
  have hUpper := WilliamsonShmoys.planar_drawingOn_edge_upper_bound_euler_exact_arcs T hV hT
  have hLower := WilliamsonShmoys.maximal_planar_drawingOn_edge_lower_bound_exact_arcs T hV hT hmax
  omega