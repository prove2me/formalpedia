-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulation_supergraph_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:55:48.34688+00:00
-- url     : https://prove2.me/submissions/1aa37b57-55c8-4749-8c75-5591ed15a7d4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_supergraph_edge_count_maximal_extension
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_supergraph_edge_count_maximal_count

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    exists M : SimpleGraph V, N <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      (M.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨M, hNM, hMdraw, hMmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulation_supergraph_edge_count_maximal_extension N hN
  refine ⟨M, hNM, hMdraw, ?_⟩
  exact WilliamsonShmoys.planar_drawing_has_triangulation_supergraph_edge_count_maximal_count
    M hV hMdraw hMmax