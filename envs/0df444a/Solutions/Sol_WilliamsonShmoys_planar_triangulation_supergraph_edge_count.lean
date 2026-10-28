-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:37:13.038622+00:00
-- url     : https://prove2.me/submissions/a980121f-2408-4ff9-bf40-7fd1b85afba3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exists_for_edge_count
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_triangulation_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hV : 3 <= Fintype.card V) :
    ∃ T : SimpleGraph V,
      (∀ {u v}, S.Adj u v → T.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hST, hTdraw, hmax⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_exists_for_edge_count S hdraw
  refine ⟨T, hST, hTdraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_completion
    T hTdraw hV hmax