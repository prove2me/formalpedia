-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_triangulation_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:34:48.324303+00:00
-- url     : https://prove2.me/submissions/0703a176-13a0-468d-9c00-70215c899d00

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_triangulation_edge_count_triangulation_extension

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hKT, hTdraw, hCount⟩ :=
    WilliamsonShmoys.maximal_drawable_graph_triangulation_edge_count_triangulation_extension
      K hK hV
  have hEq : T = K := hmax T hKT hTdraw
  rw [← hEq]
  exact hCount