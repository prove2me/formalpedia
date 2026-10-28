-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count_399d67b6_1225_43ef_9a0c_578821b9bf96
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:06:25.385104+00:00
-- url     : https://prove2.me/submissions/7f8f34d8-3b94-4039-8bed-9eb6b6192726
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_bd88397e_retry3
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_lower_bound_bd88397e_retry3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet ⊆ L.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.planar_drawing_edge_count_upper_bound_bd88397e_retry3
      L hL hCard
  have hLower :=
    WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_bd88397e_retry3
      L hL hMax hCard
  omega