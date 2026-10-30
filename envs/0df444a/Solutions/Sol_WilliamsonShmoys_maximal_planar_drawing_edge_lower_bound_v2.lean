-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:10:15.581992+00:00
-- url     : https://prove2.me/submissions/10e6f050-a1ff-465e-a98a-4b019353bd4e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_edge_bound_e951fa7c_3e6e_4109_8011_74ed7e6927fa
import Theorems.Thm_WilliamsonShmoys_planar_edgeSet_ncard_mono_for_maximal_planar_drawing_edge_lower_bound_e951fa7c_3e6e_4109_8011_74ed7e6927fa

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ X : SimpleGraph V,
      LE.le W X → WilliamsonShmoys.HasPlanarDrawingOn X → LE.le X W) :
    3 * Fintype.card V - 6 <= W.edgeSet.ncard := by
  obtain ⟨X, hWX, hX, hbound⟩ :=
    WilliamsonShmoys.planar_drawing_completion_edge_bound_e951fa7c_3e6e_4109_8011_74ed7e6927fa W hW hV
  have hXW : LE.le X W := hmax X hWX hX
  exact le_trans hbound
    (WilliamsonShmoys.planar_edgeSet_ncard_mono_for_maximal_planar_drawing_edge_lower_bound_e951fa7c_3e6e_4109_8011_74ed7e6927fa X W hXW)