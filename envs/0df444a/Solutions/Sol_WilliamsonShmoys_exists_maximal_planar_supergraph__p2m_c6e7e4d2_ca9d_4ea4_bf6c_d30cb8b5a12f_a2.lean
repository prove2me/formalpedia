-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_c6e7e4d2_ca9d_4ea4_bf6c_d30cb8b5a12f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:04:41.950937+00:00
-- url     : https://prove2.me/submissions/1622f1fe-1bc0-4305-98f3-45fc193d553c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_028c3839_39ea_4f46_a39d_0709e61e420f_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N := by
  exact WilliamsonShmoys.finite_maximal_extension__p2m_028c3839_39ea_4f46_a39d_0709e61e420f_a1
    HasPlanarDrawingOn M hM