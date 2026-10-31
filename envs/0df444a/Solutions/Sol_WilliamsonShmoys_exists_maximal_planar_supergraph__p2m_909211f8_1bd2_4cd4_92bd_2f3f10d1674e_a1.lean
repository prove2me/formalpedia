-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_909211f8_1bd2_4cd4_92bd_2f3f10d1674e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:29:11.424844+00:00
-- url     : https://prove2.me/submissions/3bec5e63-a873-4a08-9e98-189f3b8e24c6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph__p2m_dc3c3c5f_ee3d_4118_9c6e_a3edf0d67e38_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ W : SimpleGraph V, Z ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧
      ∀ X : SimpleGraph V, W ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X ≤ W := by
  exact WilliamsonShmoys.finite_maximal_supergraph__p2m_dc3c3c5f_ee3d_4118_9c6e_a3edf0d67e38_a1
    (P := WilliamsonShmoys.HasPlanarDrawingOn) Z hZ