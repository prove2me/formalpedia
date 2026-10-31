-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_extension_exists__p2m_e4b54fa0_8696_482b_974e_2350a87956d8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:54:48.703143+00:00
-- url     : https://prove2.me/submissions/df35bc15-bab0-4ec5-a9d2-0c190ae15c38
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_mono__p2m_693a0634_6764_414a_b500_9400969f72a3_a1
import Theorems.Thm_WilliamsonShmoys_finite_maximal_extension_of_downward_closed__p2m_693a0634_6764_414a_b500_9400969f72a3_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ Q : SimpleGraph V, N.edgeSet ⊆ Q.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      ∀ R : SimpleGraph V, Q.edgeSet ⊆ R.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn R → R.edgeSet = Q.edgeSet := by
  apply WilliamsonShmoys.finite_maximal_extension_of_downward_closed__p2m_693a0634_6764_414a_b500_9400969f72a3_a1
      (P := WilliamsonShmoys.HasPlanarDrawingOn) N hDraw
  intro G H hGH hH
  exact WilliamsonShmoys.planarDrawingOn_mono__p2m_693a0634_6764_414a_b500_9400969f72a3_a1 G H hGH hH