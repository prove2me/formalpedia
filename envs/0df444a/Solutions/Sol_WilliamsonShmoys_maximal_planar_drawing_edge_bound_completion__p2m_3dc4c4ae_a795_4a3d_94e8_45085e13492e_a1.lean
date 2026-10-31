-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_bound_completion__p2m_3dc4c4ae_a795_4a3d_94e8_45085e13492e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:55:41.411272+00:00
-- url     : https://prove2.me/submissions/3e993ea5-53ff-4123-8719-deb940f766ee

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_supergraph__p2m_34be30da_42b8_40a1_89e9_f0ba3aa7e7d4_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound__p2m_34be30da_42b8_40a1_89e9_f0ba3aa7e7d4_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_34be30da_42b8_40a1_89e9_f0ba3aa7e7d4_a1
      G hG
  exact ⟨H, hGH, hH,
    WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_34be30da_42b8_40a1_89e9_f0ba3aa7e7d4_a1
      H hH hCard hmax⟩