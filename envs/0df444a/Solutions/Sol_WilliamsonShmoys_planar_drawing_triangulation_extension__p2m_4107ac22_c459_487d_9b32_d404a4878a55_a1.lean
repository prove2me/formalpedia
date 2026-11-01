-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_4107ac22_c459_487d_9b32_d404a4878a55_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:53:34.22122+00:00
-- url     : https://prove2.me/submissions/738afd28-1352-47aa-bf14-74d1491bc003

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph__p2m_6683070b_8f0f_4f85_989e_81cd2560323f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_6683070b_8f0f_4f85_989e_81cd2560323f_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.maximal_drawable_supergraph__p2m_6683070b_8f0f_4f85_989e_81cd2560323f_a1
      M hM
  exact ⟨N, hMN, hN,
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6683070b_8f0f_4f85_989e_81cd2560323f_a1
      N hN hcard hmax⟩