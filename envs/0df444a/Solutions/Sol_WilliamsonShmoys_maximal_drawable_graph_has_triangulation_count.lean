-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_triangulation_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T21:55:18.365366+00:00
-- url     : https://prove2.me/submissions/cc6c8ebd-f077-4cd8-977f-f01393cf116e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_upper_bound_repair
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound_repair

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> HasPlanarDrawingOn M -> M = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hup := WilliamsonShmoys.maximal_drawable_graph_edge_upper_bound_repair L hV hL
  have hlo := WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_repair L hV hL hmax
  omega