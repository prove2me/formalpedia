-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_5f0f808e_c07c_4234_8a22_35ebffc68b17_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:08:07.030336+00:00
-- url     : https://prove2.me/submissions/df660b92-e908-41b1-ba4e-087d888604e4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_augmentation__p2m_c356afa4_3905_47c7_8a37_a6d010ebe354_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ L : SimpleGraph V, H ≤ L → L ≠ H →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hHT, hT, hTcard⟩ :=
    WilliamsonShmoys.planar_triangulation_augmentation__p2m_c356afa4_3905_47c7_8a37_a6d010ebe354_a1
      H hV hH
  have hEq : T = H := by
    by_contra hne
    exact (hmax T hHT hne) hT
  subst T
  exact hTcard