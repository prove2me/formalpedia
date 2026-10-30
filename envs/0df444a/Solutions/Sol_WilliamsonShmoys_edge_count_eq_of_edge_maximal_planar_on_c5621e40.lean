-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_eq_of_edge_maximal_planar_on_c5621e40
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:45:42.377926+00:00
-- url     : https://prove2.me/submissions/8a050c34-0ae9-42f6-ab9f-09f94a640996

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMaximal : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKDrawing, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_completion H hDrawing hV
  have hKH : K = H := hMaximal K hHK hKDrawing
  rw [← hKH]
  exact hCount