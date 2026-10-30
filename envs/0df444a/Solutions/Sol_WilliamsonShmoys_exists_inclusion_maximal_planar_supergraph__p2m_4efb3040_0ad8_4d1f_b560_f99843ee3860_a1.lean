-- Prove2me | solution 1 for WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_4efb3040_0ad8_4d1f_b560_f99843ee3860_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:36:24.14102+00:00
-- url     : https://prove2.me/submissions/2322791c-5ee9-4e97-b2c8-d4996210a861

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph__p2m_cd8388a1_00a6_4989_92c9_fa93d023609b_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V, G ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by
  exact WilliamsonShmoys.finite_maximal_supergraph__p2m_cd8388a1_00a6_4989_92c9_fa93d023609b_a1
    G HasPlanarDrawingOn hG