-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal_augmentation__p2m_be074bdb_79a8_40c0_b245_62762170066e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:39:45.446387+00:00
-- url     : https://prove2.me/submissions/65f6e444-5411-48ca-8c65-6701dc4d1fa0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_above_finite_partial_order__p2m_867a30c3_e0cd_4780_a6e7_8570584f57fd_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, K ≤ L →
          WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by
  classical
  obtain ⟨K, hJK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_above_finite_partial_order__p2m_867a30c3_e0cd_4780_a6e7_8570584f57fd_a1
      (P := WilliamsonShmoys.HasPlanarDrawingOn) J hJ
  exact ⟨K, hJK, hK, hmax⟩