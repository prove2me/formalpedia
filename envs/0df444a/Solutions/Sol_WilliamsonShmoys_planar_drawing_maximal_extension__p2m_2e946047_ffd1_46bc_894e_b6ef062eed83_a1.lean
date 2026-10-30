-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_2e946047_ffd1_46bc_894e_b6ef062eed83_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:44:48.063958+00:00
-- url     : https://prove2.me/submissions/2668ccfa-a124-40d4-b9c3-3b80aba75b30

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_simpleGraph_finite_of_fintype__p2m_c9fc3f38_cd2a_4e85_9567_ad68f211d82b_a1
import Theorems.Thm_WilliamsonShmoys_exists_maximal_above_of_finite__p2m_c9fc3f38_cd2a_4e85_9567_ad68f211d82b_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by
  letI : Finite (SimpleGraph V) :=
    WilliamsonShmoys.simpleGraph_finite_of_fintype__p2m_c9fc3f38_cd2a_4e85_9567_ad68f211d82b_a1
  exact WilliamsonShmoys.exists_maximal_above_of_finite__p2m_c9fc3f38_cd2a_4e85_9567_ad68f211d82b_a1
    L HasPlanarDrawingOn hL