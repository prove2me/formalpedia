-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_63a2cd28_190d_474c_9b63_884183b5c0a6_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:34:54.177703+00:00
-- url     : https://prove2.me/submissions/a95ad7c0-aadf-4505-8985-2292269d772b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_cdb0b6f1_a84d_40dd_8abc_1ae801f067a5_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_cdb0b6f1_a84d_40dd_8abc_1ae801f067a5_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet = N.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper :
      N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_cdb0b6f1_a84d_40dd_8abc_1ae801f067a5_a1
      N hN hCard
  have hLower :
      3 * Fintype.card V ≤ N.edgeSet.ncard + 6 :=
    WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_cdb0b6f1_a84d_40dd_8abc_1ae801f067a5_a1
      N hN hMax hCard
  omega