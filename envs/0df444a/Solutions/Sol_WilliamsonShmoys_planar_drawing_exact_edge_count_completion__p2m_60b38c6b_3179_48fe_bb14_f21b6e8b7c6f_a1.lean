-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_exact_edge_count_completion__p2m_60b38c6b_3179_48fe_bb14_f21b6e8b7c6f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:22:42.647966+00:00
-- url     : https://prove2.me/submissions/3dbefaf3-c88b-4efc-aa20-c6a47cb7e702

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension__p2m_0e3a5bf5_c35e_4938_9aa7_a032ab0de182_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count__p2m_0e3a5bf5_c35e_4938_9aa7_a032ab0de182_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hLDraw, hMax⟩ :=
    WilliamsonShmoys.maximal_drawable_extension__p2m_0e3a5bf5_c35e_4938_9aa7_a032ab0de182_a1
      K hDraw
  exact ⟨L, hKL, hLDraw,
    WilliamsonShmoys.maximal_drawing_edge_count__p2m_0e3a5bf5_c35e_4938_9aa7_a032ab0de182_a1
      L hLDraw hCard hMax⟩