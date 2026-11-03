-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper__p2m_324069a7_d0a2_45e0_94ba_3f9b77cc47fd_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:14:53.193173+00:00
-- url     : https://prove2.me/submissions/d8bbb5cb-107c-4d50-b19a-5b6f470f0e9e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_6f6a4225_6fc3_4c15_be9a_75786ea7ae4b_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_6f6a4225_6fc3_4c15_be9a_75786ea7ae4b_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    L.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  classical
  letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
    fun G => Classical.decRel G.Adj
  obtain ⟨H, hLH, hH, hmax, hle⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_6f6a4225_6fc3_4c15_be9a_75786ea7ae4b_a2
      (V := V) L hL
  have hbound :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6f6a4225_6fc3_4c15_be9a_75786ea7ae4b_a2
      H hcard hH hmax
  exact hle.trans hbound