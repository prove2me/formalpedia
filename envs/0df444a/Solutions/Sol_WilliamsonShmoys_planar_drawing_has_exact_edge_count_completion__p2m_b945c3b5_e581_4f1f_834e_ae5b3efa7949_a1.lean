-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_b945c3b5_e581_4f1f_834e_ae5b3efa7949_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:33:58.442971+00:00
-- url     : https://prove2.me/submissions/72dcf2d4-e9e6-4c03-a3c3-dafa186780ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_completion__p2m_0d4fbf3e_ba5d_4358_a028_c1fcc85193dd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_0d4fbf3e_ba5d_4358_a028_c1fcc85193dd_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hKH, hH, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_completion__p2m_0d4fbf3e_ba5d_4358_a028_c1fcc85193dd_a1
      K hK
  exact ⟨H, hKH, hH,
    WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_0d4fbf3e_ba5d_4358_a028_c1fcc85193dd_a1
      H hH hCard hMax⟩