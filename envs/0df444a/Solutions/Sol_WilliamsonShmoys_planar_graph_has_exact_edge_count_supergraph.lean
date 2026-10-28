-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_exact_edge_count_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:39:58.114012+00:00
-- url     : https://prove2.me/submissions/fe9b3f84-ed1f-4b71-8e12-d38439d33433
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_for_exact_edge_count_f2fc27dd
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_exact_edge_count_for_f2fc27dd

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, ⟨hH, hmax⟩⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph_for_exact_edge_count_f2fc27dd
      G hG
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_has_exact_edge_count_for_f2fc27dd
      H hV hH hmax
  exact ⟨H, hGH, hH, hcount⟩