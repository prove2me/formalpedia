-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_completion__p2m_bcf9fc22_a10c_472d_8ae6_0fdb1da6c723_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:25:41.212958+00:00
-- url     : https://prove2.me/submissions/79cab3a4-3946-4c21-b099-95c12b2eb78e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_236ff196_eb97_4260_bf50_22869620a85a_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      (∀ u v, K.Adj u v → L.Adj u v) ∧
      (∀ M : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn M →
        (∀ u v, L.Adj u v → M.Adj u v) →
        ∀ u v, M.Adj u v → L.Adj u v) := by
  exact WilliamsonShmoys.finite_maximal_extension__p2m_236ff196_eb97_4260_bf50_22869620a85a_a1
    K WilliamsonShmoys.HasPlanarDrawingOn hK
