-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion_edge_bound_e951fa7c_3e6e_4109_8011_74ed7e6927fa
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:34:29.356052+00:00
-- url     : https://prove2.me/submissions/1347788f-abb2-4c5a-9627-59cccc46dd32

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_e951fa7c_3e6e_4109_8011_74ed7e6927fa
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_e951fa7c_3e6e_4109_8011_74ed7e6927fa

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 <= Fintype.card V) :
    ∃ X : SimpleGraph V,
      W ≤ X ∧
      WilliamsonShmoys.HasPlanarDrawingOn X ∧
      3 * Fintype.card V - 6 <= X.edgeSet.ncard := by
  obtain ⟨X, hWX, hX, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_e951fa7c_3e6e_4109_8011_74ed7e6927fa W hW
  exact ⟨X, hWX, hX,
    WilliamsonShmoys.maximal_planar_edge_bound_e951fa7c_3e6e_4109_8011_74ed7e6927fa X hX hmax hV⟩