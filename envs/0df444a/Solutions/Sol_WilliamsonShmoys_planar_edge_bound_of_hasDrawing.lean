-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_of_hasDrawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:33:51.55706+00:00
-- url     : https://prove2.me/submissions/c84ffcb0-367b-454c-ade7-13935f10141a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_maximal_planar_drawing

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKplanar, hKmax, hEdges⟩ :=
    WilliamsonShmoys.planar_drawing_finite_maximal_supergraph H hV hHplanar
  have hBound := WilliamsonShmoys.planar_edge_bound_of_maximal_planar_drawing
    K hV hKplanar hKmax
  omega