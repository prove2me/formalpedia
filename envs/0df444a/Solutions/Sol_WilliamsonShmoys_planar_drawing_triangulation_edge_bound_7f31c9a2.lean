-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_edge_bound_7f31c9a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:55:48.77936+00:00
-- url     : https://prove2.me/submissions/e012f8c1-1793-4ff2-8c75-b65012858416
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximizer_exists_7f31c9a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_7f31c9a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ u v, K.Adj u v → H.Adj u v) ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hKH, hDrawH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximizer_exists_7f31c9a2 K hDraw
  refine ⟨H, hKH, ?_, hDrawH, ?_⟩
  · exact hmax K (by intro u v huv; exact huv) hDraw
  · exact WilliamsonShmoys.maximal_planar_edge_count_7f31c9a2
      K hCard H hKH hDrawH hmax