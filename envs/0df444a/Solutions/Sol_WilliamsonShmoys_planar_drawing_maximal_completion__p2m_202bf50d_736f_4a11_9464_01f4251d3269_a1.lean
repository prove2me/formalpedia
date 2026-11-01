-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_completion__p2m_202bf50d_736f_4a11_9464_01f4251d3269_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:18:06.863816+00:00
-- url     : https://prove2.me/submissions/8329ca54-064b-4e28-9361-247847672661

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph__p2m_a34ee183_b91b_4a67_873f_251f94ba9522_a2
import Theorems.Thm_WilliamsonShmoys_edgeFinset_card_le_edgeSet_ncard_of_subset__p2m_a34ee183_b91b_4a67_873f_251f94ba9522_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeFinset.card ≤ H.edgeSet.ncard ∧
      (∀ J : SimpleGraph V,
        H.edgeSet ⊆ J.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn J →
        J.edgeSet ⊆ H.edgeSet) := by
  classical
  obtain ⟨H, hKH, hH, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_supergraph__p2m_a34ee183_b91b_4a67_873f_251f94ba9522_a2
      K WilliamsonShmoys.HasPlanarDrawingOn hK
  refine ⟨H, hKH, hH, ?_, hmax⟩
  exact WilliamsonShmoys.edgeFinset_card_le_edgeSet_ncard_of_subset__p2m_a34ee183_b91b_4a67_873f_251f94ba9522_a2
    K H hKH