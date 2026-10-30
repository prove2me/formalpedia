-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_with_exact_edge_count_05b21acc_4700_43ee_9041_67ebfdbea9d3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:35:37.768843+00:00
-- url     : https://prove2.me/submissions/9e498355-f542-4e33-b878-20ec6e1a5c58

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_cardinal_max_7f31c9a2
import Theorems.Thm_WilliamsonShmoys_max_cardinal_drawable_edge_count_7f31c9a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨K, hGK, hKDraw, hMax⟩ :=
    WilliamsonShmoys.drawable_supergraph_cardinal_max_7f31c9a2 G hDraw
  refine ⟨K, hGK, hKDraw, ?_⟩
  exact WilliamsonShmoys.max_cardinal_drawable_edge_count_7f31c9a2 K hKDraw hMax hCard