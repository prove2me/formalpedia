-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_extension_for_triangulation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T21:17:57.730086+00:00
-- url     : https://prove2.me/submissions/6ad03cbd-48a5-4271-b8ba-f3113a98b82c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_simpleGraph_supergraph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_simpleGraph_supergraph
      G HasPlanarDrawingOn hG
  exact ⟨K, hGK, hK, fun L hKL hL => hmax L hKL hL⟩