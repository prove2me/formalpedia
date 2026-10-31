-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_69a4b515_b2d1_4c44_a03e_fe4ffa3a8acf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:17:05.639076+00:00
-- url     : https://prove2.me/submissions/7ef0c026-ec02-4091-8ceb-cd53f8d645d6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_predicate_maximal_extension__p2m_5044aa6a_f37f_461e_b852_1ca819824640_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V, N ≤ P →
        WilliamsonShmoys.HasPlanarDrawingOn P → P = N := by
  exact WilliamsonShmoys.finite_predicate_maximal_extension__p2m_5044aa6a_f37f_461e_b852_1ca819824640_a1
    (P := WilliamsonShmoys.HasPlanarDrawingOn) M hM