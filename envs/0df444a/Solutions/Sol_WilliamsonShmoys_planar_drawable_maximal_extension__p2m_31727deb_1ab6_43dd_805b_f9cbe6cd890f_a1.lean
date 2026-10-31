-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_maximal_extension__p2m_31727deb_1ab6_43dd_805b_f9cbe6cd890f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:16:29.981857+00:00
-- url     : https://prove2.me/submissions/13f2843c-529c-4727-bb13-3ad97d990f6c

import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_76998751_2d00_4690_8bec_fa846df46441_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (Y : SimpleGraph V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V, Y ≤ Z ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      ∀ W : SimpleGraph V, Z ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W ≤ Z := by
  exact WilliamsonShmoys.finite_maximal_extension__p2m_76998751_2d00_4690_8bec_fa846df46441_a1
    (P := WilliamsonShmoys.HasPlanarDrawingOn) Y hY