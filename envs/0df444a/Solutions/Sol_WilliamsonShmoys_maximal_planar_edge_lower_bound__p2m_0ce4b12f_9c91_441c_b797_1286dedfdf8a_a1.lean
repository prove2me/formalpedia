-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_0ce4b12f_9c91_441c_b797_1286dedfdf8a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:21:06.944602+00:00
-- url     : https://prove2.me/submissions/b1e2d979-1a86-430a-b414-d1783c57dbeb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_b945c3b5_e581_4f1f_834e_ae5b3efa7949_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by
  obtain ⟨H, hKH, hH, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_b945c3b5_e581_4f1f_834e_ae5b3efa7949_a1
      K hK hCard
  have hHK : H.edgeSet ⊆ K.edgeSet := hmax H hKH hH
  have hEq : K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
    rw [Set.Subset.antisymm hKH hHK]
    exact hCount
  omega