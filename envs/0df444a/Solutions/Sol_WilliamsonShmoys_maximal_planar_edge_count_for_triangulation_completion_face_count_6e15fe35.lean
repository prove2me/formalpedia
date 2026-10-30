-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_completion_face_count_6e15fe35
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:28:27.774878+00:00
-- url     : https://prove2.me/submissions/aa797ffa-4f02-4a98-a237-808943662880

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_count_upper_bound_from_drawing_6e15fe35
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_from_drawing_6e15fe35

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → M = N)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound_from_drawing_6e15fe35
    M hM hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound_from_drawing_6e15fe35
    M hM hMax hCard
  omega