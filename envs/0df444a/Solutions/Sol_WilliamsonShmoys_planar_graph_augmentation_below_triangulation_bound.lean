-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_augmentation_below_triangulation_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:52:56.734673+00:00
-- url     : https://prove2.me/submissions/7f5eab78-95ad-44ba-aea0-88678ef35042
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_maximal_supergraph_for_augmentation
import Theorems.Thm_WilliamsonShmoys_maximal_drawingOn_edge_bound_for_augmentation

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hsmall : 3 * Fintype.card V > L.edgeSet.ncard + 6) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M ≠ L := by
  obtain ⟨M, hLM, hMdraw, hMmax⟩ :=
    WilliamsonShmoys.planarDrawingOn_maximal_supergraph_for_augmentation L hLdraw
  have hMbound :=
    WilliamsonShmoys.maximal_drawingOn_edge_bound_for_augmentation M hMdraw hCard hMmax
  refine ⟨M, hLM, hMdraw, ?_⟩
  intro hEq
  subst M
  exact (not_le_of_gt hsmall) hMbound