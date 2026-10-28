-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_triangulated_augmentation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:16:21.313786+00:00
-- url     : https://prove2.me/submissions/bd74308c-19e0-49ec-b8db-909e7d4fe7ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_drawable_augmentation_retry2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation_edge_count_retry2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hUdraw : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hCard : 3 <= Fintype.card V) :
    Exists fun W : SimpleGraph V =>
      U <= W /\ WilliamsonShmoys.HasPlanarDrawingOn W /\
      3 * Fintype.card V = W.edgeSet.ncard + 6 := by
  obtain ⟨W, hUW, hWdraw, hmax⟩ :=
    WilliamsonShmoys.drawable_graph_has_maximal_drawable_augmentation_retry2 U hUdraw
  refine ⟨W, hUW, hWdraw, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count_retry2
    W hWdraw hCard hmax