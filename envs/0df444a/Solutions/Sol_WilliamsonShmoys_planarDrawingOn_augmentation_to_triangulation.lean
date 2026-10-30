-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_augmentation_to_triangulation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:05:26.277997+00:00
-- url     : https://prove2.me/submissions/d64362bd-7b43-4b69-b067-31527d7c69e8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_maximal_supergraph_fe74ac1b_216e_4ca8_b058_0b3c4a531007
import Theorems.Thm_WilliamsonShmoys_maximal_planarDrawingOn_edge_count_fe74ac1b_216e_4ca8_b058_0b3c4a531007

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hGK, hKDraw, hMax⟩ :=
    WilliamsonShmoys.planarDrawingOn_maximal_supergraph_fe74ac1b_216e_4ca8_b058_0b3c4a531007
      G hDraw
  exact ⟨K, hGK, hKDraw,
    WilliamsonShmoys.maximal_planarDrawingOn_edge_count_fe74ac1b_216e_4ca8_b058_0b3c4a531007
      K hKDraw hCard hMax⟩