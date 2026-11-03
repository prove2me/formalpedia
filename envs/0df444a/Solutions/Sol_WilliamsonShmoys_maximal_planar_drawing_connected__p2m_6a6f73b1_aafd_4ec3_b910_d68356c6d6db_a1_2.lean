-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_connected__p2m_6a6f73b1_aafd_4ec3_b910_d68356c6d6db_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:25:47.911135+00:00
-- url     : https://prove2.me/submissions/cf81912b-4ec9-40d7-abc7-cfefa0de6672

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_unreachable_pair_of_not_connected_of_card_ge_three__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a2
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_unreachable_vertices__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G)
    (hcard : 3 ≤ Fintype.card V) :
    G.Connected := by
  by_contra hnot
  obtain ⟨u, v, huv⟩ :=
    WilliamsonShmoys.exists_unreachable_pair_of_not_connected_of_card_ge_three__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a2
      G hnot hcard
  obtain ⟨K, hGK, hKG, hK⟩ :=
    WilliamsonShmoys.planar_add_edge_between_unreachable_vertices__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a1
      G hG u v huv
  exact hKG (hmax K hGK hK)