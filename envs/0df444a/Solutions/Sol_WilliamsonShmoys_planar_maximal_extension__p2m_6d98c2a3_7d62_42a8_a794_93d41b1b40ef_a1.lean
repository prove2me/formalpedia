-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_extension__p2m_6d98c2a3_7d62_42a8_a794_93d41b1b40ef_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:57:06.469199+00:00
-- url     : https://prove2.me/submissions/6d4f0721-df3f-4796-b643-fc4b9c8e3847

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_card_maximal_planar_extension__p2m_5d6e3508_c11e_4337_a63b_6a8f12f05f58_a2
import Theorems.Thm_WilliamsonShmoys_simpleGraph_eq_of_le_of_edgeSet_ncard_le__p2m_5d6e3508_c11e_4337_a63b_6a8f12f05f58_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by
  obtain ⟨K, hNK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_card_maximal_planar_extension__p2m_5d6e3508_c11e_4337_a63b_6a8f12f05f58_a2 N hN
  refine ⟨K, hNK, hK, ?_⟩
  intro L hKL hL
  have hEq :=
    WilliamsonShmoys.simpleGraph_eq_of_le_of_edgeSet_ncard_le__p2m_5d6e3508_c11e_4337_a63b_6a8f12f05f58_a2
      K L hKL (hmax L hKL hL)
  exact hEq.symm.le