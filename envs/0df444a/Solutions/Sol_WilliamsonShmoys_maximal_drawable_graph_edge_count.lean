-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:19:27.878986+00:00
-- url     : https://prove2.me/submissions/15ab202e-2542-4f77-8b38-f7c9dc641b18

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_simple_planar_drawing_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_simple_graph_edge_count_lower_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hMax : ∀ U : SimpleGraph V,
      T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hlow := WilliamsonShmoys.maximal_drawable_simple_graph_edge_count_lower_bound T hV hT hMax
  have hupp := WilliamsonShmoys.simple_planar_drawing_edge_count_upper_bound T hV hT
  omega