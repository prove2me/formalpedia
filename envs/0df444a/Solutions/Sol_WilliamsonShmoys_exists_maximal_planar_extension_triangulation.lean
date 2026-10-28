-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension_triangulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:22:28.831134+00:00
-- url     : https://prove2.me/submissions/3c265251-36a4-4652-a680-89dfaf7636f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_on_finite_vertices
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_finite_planar_drawing

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hLM, hDrawM, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph_on_finite_vertices L hV hDraw
  refine ⟨M, hLM, hDrawM, hMax, ?_⟩
  exact WilliamsonShmoys.edge_count_of_maximal_finite_planar_drawing M hV hDrawM hMax