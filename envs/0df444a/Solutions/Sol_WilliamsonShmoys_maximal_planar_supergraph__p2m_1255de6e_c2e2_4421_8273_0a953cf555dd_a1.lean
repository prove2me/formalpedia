-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph__p2m_1255de6e_c2e2_4421_8273_0a953cf555dd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:21:18.898577+00:00
-- url     : https://prove2.me/submissions/78fceea9-8af9-43dc-b3fc-f7e5b1b1f56b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph__p2m_fe1a9c4f_5aad_4a32_a050_44f6e8cc3efe_a1
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_subgraph__p2m_fe1a9c4f_5aad_4a32_a050_44f6e8cc3efe_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J ≤ H := by
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_supergraph__p2m_fe1a9c4f_5aad_4a32_a050_44f6e8cc3efe_a1
      K HasPlanarDrawingOn hK
      (by
        intro G H hGH hH
        exact WilliamsonShmoys.planarDrawingOn_subgraph__p2m_fe1a9c4f_5aad_4a32_a050_44f6e8cc3efe_a1
          hGH hH)
  exact ⟨H, hKH, hH, hmax⟩