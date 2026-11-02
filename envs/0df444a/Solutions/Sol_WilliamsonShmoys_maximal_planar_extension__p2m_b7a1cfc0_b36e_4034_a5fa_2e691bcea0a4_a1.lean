-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension__p2m_b7a1cfc0_b36e_4034_a5fa_2e691bcea0a4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:06:35.03677+00:00
-- url     : https://prove2.me/submissions/27c65fa3-3ac1-4c97-922d-8c22c4a32aa5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_exists_maximal_element_above_finite__p2m_ff2c7fc5_47bb_41b0_9771_afa052fe6028_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    exists_maximal_element_above_finite__p2m_ff2c7fc5_47bb_41b0_9771_afa052fe6028_a1
      (P := WilliamsonShmoys.HasPlanarDrawingOn) K hK
  exact ⟨L, hKL, hL, fun M hLM hM => hmax M hLM hM⟩
