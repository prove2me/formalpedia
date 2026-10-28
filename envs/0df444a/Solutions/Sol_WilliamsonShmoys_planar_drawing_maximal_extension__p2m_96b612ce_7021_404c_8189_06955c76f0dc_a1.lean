-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_96b612ce_7021_404c_8189_06955c76f0dc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:08:00.75509+00:00
-- url     : https://prove2.me/submissions/3b67d337-a639-4e8f-9ac3-c9b7ce26b299

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_for_property__p2m_d7f8daf2_7f47_4b31_bf7f_d34fcebb1d15_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M = L := by
  exact WilliamsonShmoys.exists_maximal_extension_for_property__p2m_d7f8daf2_7f47_4b31_bf7f_d34fcebb1d15_a1
    K WilliamsonShmoys.HasPlanarDrawingOn hK