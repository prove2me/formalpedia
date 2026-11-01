-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_b4fc0ec6_9094_46c1_821a_02fa395e6854_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:00:49.628517+00:00
-- url     : https://prove2.me/submissions/4429be2c-b1cb-4cf2-a779-c992674c3be6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_of_finite_predicate__p2m_c3e4c921_775b_4afc_815f_a590e3d69c46_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = N := by
  exact WilliamsonShmoys.exists_maximal_extension_of_finite_predicate__p2m_c3e4c921_775b_4afc_815f_a590e3d69c46_a1
    (P := WilliamsonShmoys.HasPlanarDrawingOn) M hM