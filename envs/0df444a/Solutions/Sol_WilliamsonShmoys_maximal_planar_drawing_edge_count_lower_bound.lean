-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:01:26.74543+00:00
-- url     : https://prove2.me/submissions/2837c936-d3c9-41fd-a4d2-3447b38965bf

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_completion

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDrawing : HasPlanarDrawingOn H)
    (hMaximal : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hKDrawing, hKCount⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulated_completion H hDrawing hV
  have hKH : K = H := hMaximal K hHK hKDrawing
  subst K
  exact le_of_eq hKCount