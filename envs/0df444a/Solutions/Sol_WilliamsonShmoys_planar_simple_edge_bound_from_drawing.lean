-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_bound_from_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:01:54.468993+00:00
-- url     : https://prove2.me/submissions/220193bc-7710-42e9-8196-53cb9abbf520

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_with_three_vertices
import Theorems.Thm_WilliamsonShmoys_planar_connected_simple_edge_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKConnected, hKDrawing, hEdgeCount⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation_with_three_vertices H hH hV
  have hBound := WilliamsonShmoys.planar_connected_simple_edge_bound K hKConnected hKDrawing hV
  omega