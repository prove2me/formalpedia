-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_maximal__p2m_adb36ea0_1077_447f_b2c5_a4177e2cdb6e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:03:41.960148+00:00
-- url     : https://prove2.me/submissions/cbd65323-3be0-4888-b1f8-22ebd651ea80

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite__p2m_1bbb274f_042a_4c5e_8e43_fd05505ca5a4_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, HasPlanarDrawingOn K ∧
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      (∀ L : SimpleGraph V, HasPlanarDrawingOn L →
        (∀ u v, K.Adj u v → L.Adj u v) →
        (∀ u v, L.Adj u v → K.Adj u v)) := by
  exact WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_1bbb274f_042a_4c5e_8e43_fd05505ca5a4_a1
    H HasPlanarDrawingOn hH