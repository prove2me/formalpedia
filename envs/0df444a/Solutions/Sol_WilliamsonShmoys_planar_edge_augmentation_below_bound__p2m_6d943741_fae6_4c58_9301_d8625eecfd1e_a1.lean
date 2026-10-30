-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_below_bound__p2m_6d943741_fae6_4c58_9301_d8625eecfd1e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:33:49.019962+00:00
-- url     : https://prove2.me/submissions/e1987904-f11c-465b-ac75-e32d1eba822e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hE : K.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ L : SimpleGraph V, K < L ∧ HasPlanarDrawingOn L := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion K hK hV
  refine ⟨L, ?_, hL⟩
  have hne : K ≠ L := by
    intro hEq
    rw [← hEq] at hcount
    omega
  exact lt_of_le_of_ne hKL hne