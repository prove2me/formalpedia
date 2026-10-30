-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_below_bound__p2m_03ed2ab0_efc9_4bea_b7ff_50f9e41807dc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:51:40.287168+00:00
-- url     : https://prove2.me/submissions/6eb3fca0-9f42-4f58-9b03-5df597cabfe9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_96b612ce_7021_404c_8189_06955c76f0dc_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_96b612ce_7021_404c_8189_06955c76f0dc_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hBelow : K.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ L : SimpleGraph V, K < L ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_96b612ce_7021_404c_8189_06955c76f0dc_a1
      K hK
  have hLower :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_96b612ce_7021_404c_8189_06955c76f0dc_a1
      L hL hMax hCard
  have hNe : K ≠ L := by
    intro hEq
    subst L
    omega
  exact ⟨L, lt_of_le_of_ne hKL hNe, hL⟩