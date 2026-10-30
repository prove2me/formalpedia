-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_d5ea2124_1838_4ceb_a0a8_373ec58ed0bb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:42:00.446826+00:00
-- url     : https://prove2.me/submissions/f8493853-1b2b-4280-a197-f491ca6caf77

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet ->
      HasPlanarDrawingOn L ->
      Set.Subset L.edgeSet K.edgeSet) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hLDraw, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count
      K hCard hDraw
  have hEdgeSubset : Set.Subset K.edgeSet L.edgeSet :=
    SimpleGraph.edgeSet_subset_edgeSet.mpr hKL
  have hReverse : Set.Subset L.edgeSet K.edgeSet := hMax L hEdgeSubset hLDraw
  have hEq : K.edgeSet = L.edgeSet := Set.Subset.antisymm hEdgeSubset hReverse
  rw [← hEq] at hCount
  omega