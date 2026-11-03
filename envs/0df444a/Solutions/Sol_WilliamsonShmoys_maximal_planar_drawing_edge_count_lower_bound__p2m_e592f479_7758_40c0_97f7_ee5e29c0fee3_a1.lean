-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_e592f479_7758_40c0_97f7_ee5e29c0fee3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:02:34.882471+00:00
-- url     : https://prove2.me/submissions/71adccc9-a065-4b87-99da-3b84017efc7d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_triangulated_supergraph__p2m_cf161613_a0bb_4259_95d5_c320f30b7319_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨N, hMN, hNdraw, hNcard⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_triangulated_supergraph__p2m_cf161613_a0bb_4259_95d5_c320f30b7319_a1
      M hM hCard
  have hNM : N ≤ M := hMax N hMN hNdraw
  have hEq : N = M := le_antisymm hNM hMN
  have hCount : M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
    rw [← hEq]
    exact hNcard
  rw [hCount]