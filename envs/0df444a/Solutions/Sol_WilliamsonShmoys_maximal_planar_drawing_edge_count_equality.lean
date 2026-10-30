-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_equality
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:48:55.215865+00:00
-- url     : https://prove2.me/submissions/d5a028f9-1bb8-4a42-81af-422441211408

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_simple_graph_edge_upper_bound_v2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ X : SimpleGraph V,
      LE.le W X → WilliamsonShmoys.HasPlanarDrawingOn X → LE.le X W) :
    W.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper :=
    WilliamsonShmoys.planar_drawing_simple_graph_edge_upper_bound_v2 W hW hV
  have hlower :=
    WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_v2 W hW hV hmax
  omega
