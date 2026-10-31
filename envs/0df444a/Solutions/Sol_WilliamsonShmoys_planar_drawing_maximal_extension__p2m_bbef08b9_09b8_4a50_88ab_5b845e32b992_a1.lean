-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_bbef08b9_09b8_4a50_88ab_5b845e32b992_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:00:45.080994+00:00
-- url     : https://prove2.me/submissions/e972971f-66db-44b8-ba88-35b6ee845329

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_predicate_maximal_extension__p2m_06ff79b1_005f_4343_ad7e_d750b7a6fe7f_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by
  exact WilliamsonShmoys.finite_predicate_maximal_extension__p2m_06ff79b1_005f_4343_ad7e_d750b7a6fe7f_a1
    WilliamsonShmoys.HasPlanarDrawingOn L hL