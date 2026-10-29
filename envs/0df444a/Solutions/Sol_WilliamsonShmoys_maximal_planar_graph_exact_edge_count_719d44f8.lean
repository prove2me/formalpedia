-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_exact_edge_count_719d44f8
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:28:51.506888+00:00
-- url     : https://prove2.me/submissions/cac44006-e2e0-49a6-9a6e-acf5b4a6b1aa

import Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_exact_edge_count_3e869d1e_d221_44f3_8f2b_71d5fc6eb8db

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V,
      G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hGK, hKdraw, hKcount⟩ :=
    WilliamsonShmoys.planar_drawing_augmentation_exact_edge_count_3e869d1e_d221_44f3_8f2b_71d5fc6eb8db
      G hV hG
  have hKG : K = G := hmax K hGK hKdraw
  rw [← hKG]
  exact hKcount