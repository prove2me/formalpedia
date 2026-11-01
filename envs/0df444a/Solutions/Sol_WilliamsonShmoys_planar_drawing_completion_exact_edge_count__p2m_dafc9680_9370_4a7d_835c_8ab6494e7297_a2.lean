-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion_exact_edge_count__p2m_dafc9680_9370_4a7d_835c_8ab6494e7297_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:11:37.577938+00:00
-- url     : https://prove2.me/submissions/ef6440bc-4143-4fb6-ae0b-3469e362edde

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_completion__p2m_202bf50d_736f_4a11_9464_01f4251d3269_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_202bf50d_736f_4a11_9464_01f4251d3269_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeFinset.card ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨H, hKH, hH, hcardle, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_completion__p2m_202bf50d_736f_4a11_9464_01f4251d3269_a1
      K hcard hK
  exact ⟨H, hKH, hH, hcardle,
    WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_202bf50d_736f_4a11_9464_01f4251d3269_a1
      H hcard hH hmax⟩