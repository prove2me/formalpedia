-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_finite_maximal_extension__p2m_c5c73f75_8c1e_44ef_9deb_26150704a428_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:04:17.032272+00:00
-- url     : https://prove2.me/submissions/8a9ac464-1854-43d4-97be-d5ccbcf06803

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite__p2m_dfccf1a0_d8d5_4c21_b668_467919d5e80f_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun H : SimpleGraph V =>
      And (K <= H) (And (WilliamsonShmoys.HasPlanarDrawingOn H)
        (forall J : SimpleGraph V, H <= J ->
          WilliamsonShmoys.HasPlanarDrawingOn J -> H = J)) := by
  exact WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_dfccf1a0_d8d5_4c21_b668_467919d5e80f_a1
    K WilliamsonShmoys.HasPlanarDrawingOn hK