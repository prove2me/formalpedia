-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_arcs
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:28:38.99367+00:00
-- url     : https://prove2.me/submissions/7fb9fe39-7581-479e-ab3e-c082935e1fca

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_same_vertex_triangulation_with_exact_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 <= Fintype.card V)
    (hMaximal : forall K : SimpleGraph V,
      N <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hNK, hKDrawing, hCount⟩ :=
    WilliamsonShmoys.exists_same_vertex_triangulation_with_exact_edge_count
      N hDrawing hCard
  have hKN : K = N := hMaximal K hNK hKDrawing
  simpa [hKN] using hCount
