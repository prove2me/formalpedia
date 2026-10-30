-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_edgeSet_ncard_ge
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:46:53.579418+00:00
-- url     : https://prove2.me/submissions/42cd5fb2-8e1b-4f89-8716-d26ca95a5c0c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_with_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J) :
    3 * Fintype.card V - 6 ≤ J.edgeSet.ncard := by
  obtain ⟨K, hJK, hKDraw, hKBound⟩ :=
    WilliamsonShmoys.exists_drawable_supergraph_with_edge_bound J hDraw hCard
  have hKJ : K = J := hMax K hJK hKDraw
  simpa [hKJ] using hKBound