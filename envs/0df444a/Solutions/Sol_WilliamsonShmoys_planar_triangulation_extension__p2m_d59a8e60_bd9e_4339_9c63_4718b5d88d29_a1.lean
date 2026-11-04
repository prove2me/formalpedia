-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_d59a8e60_bd9e_4339_9c63_4718b5d88d29_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:59:16.327612+00:00
-- url     : https://prove2.me/submissions/4112ee82-d43e-4d0c-851d-30f130e57f93

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_4ae5175f_f6af_4329_a008_007eae5b47e6_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_4ae5175f_f6af_4329_a008_007eae5b47e6_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
        L.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_4ae5175f_f6af_4329_a008_007eae5b47e6_a2
      K hV hK
  refine ⟨L, hKL, hL, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_4ae5175f_f6af_4329_a008_007eae5b47e6_a2
    L hV hL hmax