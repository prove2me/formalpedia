-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_extension__p2m_986cca2a_af96_41ca_97f1_9fc97c42977c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:31:53.948949+00:00
-- url     : https://prove2.me/submissions/d81e24cf-4f2a-4b4b-a938-297347ccf1be

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_finite_hereditary_maximal_extension__p2m_3f244f53_8936_4715_8547_0063dd70ff12_a1
import Theorems.Thm_planar_drawing_on_subgraph__p2m_3f244f53_8936_4715_8547_0063dd70ff12_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V,
        K ≤ J →
        WilliamsonShmoys.HasPlanarDrawingOn J →
        H ≤ J → J = H := by
  exact finite_hereditary_maximal_extension__p2m_3f244f53_8936_4715_8547_0063dd70ff12_a1
    K WilliamsonShmoys.HasPlanarDrawingOn hK
    (by
      intro G H hGH hH
      exact planar_drawing_on_subgraph__p2m_3f244f53_8936_4715_8547_0063dd70ff12_a1 hGH hH)