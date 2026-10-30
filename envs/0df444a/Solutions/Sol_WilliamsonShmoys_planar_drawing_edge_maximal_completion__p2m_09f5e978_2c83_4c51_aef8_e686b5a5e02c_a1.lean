-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_maximal_completion__p2m_09f5e978_2c83_4c51_aef8_e686b5a5e02c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:38:48.97481+00:00
-- url     : https://prove2.me/submissions/1c365bf2-fc11-4c07-84e0-3f34b8310eaf

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_supergraph_maximality__p2m_8549c90d_5e03_4132_87df_05240f9d6920_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V, H ≤ J ∧ HasPlanarDrawingOn J ∧
      (∀ K : SimpleGraph V, J ≤ K → HasPlanarDrawingOn K → K ≤ J) := by
  exact WilliamsonShmoys.finite_supergraph_maximality__p2m_8549c90d_5e03_4132_87df_05240f9d6920_a1
    HasPlanarDrawingOn H hH