-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph_719d44f8
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:17:38.261097+00:00
-- url     : https://prove2.me/submissions/b66119a7-3767-43c3-8778-39c00d3f49e2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_simpleGraph_family

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  obtain ⟨K, hKdraw, hKmax⟩ :=
    WilliamsonShmoys.exists_maximal_simpleGraph_family
      (fun G : SimpleGraph V => H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)
      ⟨H, le_rfl, hH⟩
  refine ⟨K, hKdraw.1, hKdraw.2, ?_⟩
  intro L hKL hLdraw
  exact hKmax L ⟨le_trans hKdraw.1 hKL, hLdraw⟩ hKL