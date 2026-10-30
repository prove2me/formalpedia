-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_euler_edge_count_26473918
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:21:36.536639+00:00
-- url     : https://prove2.me/submissions/40f36da7-4376-474c-a8ca-9ea438c50ef2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_26473918
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_26473918

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hGK, hKdraw, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_26473918 G hGdraw
  refine ⟨K, hGK, hKdraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count_26473918
    K hKdraw hCard hmax
