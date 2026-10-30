-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_triangulated_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:56:58.87351+00:00
-- url     : https://prove2.me/submissions/89257ccf-d8c8-40bf-83d1-7f65d11cc2a5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_extension_792d6233_0413_48c2_8c4d_fb4d15268d51
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_792d6233_0413_48c2_8c4d_fb4d15268d51

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hWdraw : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ X : SimpleGraph V,
      W ≤ X ∧ WilliamsonShmoys.HasPlanarDrawingOn X ∧
        3 * Fintype.card V = X.edgeSet.ncard + 6 := by
  obtain ⟨X, hWX, hXdraw, hMax⟩ :=
    WilliamsonShmoys.drawable_graph_has_maximal_extension_792d6233_0413_48c2_8c4d_fb4d15268d51
      W hWdraw
  exact ⟨X, hWX, hXdraw,
    WilliamsonShmoys.maximal_drawable_graph_edge_count_792d6233_0413_48c2_8c4d_fb4d15268d51
      X hCard hXdraw hMax⟩