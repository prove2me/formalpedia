-- Prove2me | solution 1 for WilliamsonShmoys.exists_isMaximalPlanarSupergraph__p2m_252969a2_5705_4ea9_b97e_d995b4f5b608_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:19:45.259414+00:00
-- url     : https://prove2.me/submissions/504adc99-d0cc-4aea-a6ef-ff62506af410
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_element_above_of_finite_partialOrder__p2m_af13f63f_cd05_40af_9e3b_bd5fcae2a11f_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by
  classical
  exact WilliamsonShmoys.exists_maximal_element_above_of_finite_partialOrder__p2m_af13f63f_cd05_40af_9e3b_bd5fcae2a11f_a1
    (α := SimpleGraph V) (P := WilliamsonShmoys.HasPlanarDrawingOn) L hDraw