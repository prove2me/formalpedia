-- Prove2me | solution 1 for WilliamsonShmoys.exists_triangulated_planar_completion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:28:02.319926+00:00
-- url     : https://prove2.me/submissions/461d5239-adaa-495e-82c6-31ad1c02d575

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_completion_exists_maximal_drawable_supergraph_6a2f736f
import Theorems.Thm_WilliamsonShmoys_completion_edge_count_of_maximal_drawable_6a2f736f
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.completion_exists_maximal_drawable_supergraph_6a2f736f G hG
  exact ⟨K, hGK, hK,
    WilliamsonShmoys.completion_edge_count_of_maximal_drawable_6a2f736f K hV hK hmax⟩