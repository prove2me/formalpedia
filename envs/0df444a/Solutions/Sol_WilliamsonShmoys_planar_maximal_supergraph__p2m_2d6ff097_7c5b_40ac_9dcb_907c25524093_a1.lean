-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_supergraph__p2m_2d6ff097_7c5b_40ac_9dcb_907c25524093_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:13:57.82896+00:00
-- url     : https://prove2.me/submissions/34ddd1e1-42a0-4bf1-8cdb-1be7a1c4b735

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_exists_maximal_supergraph_pred__p2m_b455b77e_ddaf_4a1e_8731_97164a818640_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      (∀ {u v : V}, P.Adj u v → Q.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      (∀ R : SimpleGraph V,
        (∀ {u v : V}, Q.Adj u v → R.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn R →
        R = Q) := by
  exact WilliamsonShmoys.finite_exists_maximal_supergraph_pred__p2m_b455b77e_ddaf_4a1e_8731_97164a818640_a1
    P WilliamsonShmoys.HasPlanarDrawingOn hP