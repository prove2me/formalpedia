-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_00e8ebb5_9f6a_4f3b_a13c_8345d9aaf556_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:24:33.413968+00:00
-- url     : https://prove2.me/submissions/c61dffc6-792d-4fe4-9718-c4bcface24b4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_exact_edge_count__p2m_a712b8ac_2693_4359_b1bf_8163c9ce4446_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
      HasPlanarDrawingOn K → H.edgeSet = K.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hSub, hKDraw, hKCount⟩ :=
    WilliamsonShmoys.planar_completion_exact_edge_count__p2m_a712b8ac_2693_4359_b1bf_8163c9ce4446_a1
      H hDraw hCard
  have hEq := hMax K hSub hKDraw
  rw [hEq]
  exact hKCount
