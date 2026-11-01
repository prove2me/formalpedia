-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_connected__p2m_6a6f73b1_aafd_4ec3_b910_d68356c6d6db_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:10:32.726456+00:00
-- url     : https://prove2.me/submissions/e1d0df44-c0e8-458f-b8b7-45ad592ee0a2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_unreachable_pair_of_not_connected__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a1
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
    WilliamsonShmoys.exists_unreachable_pair_of_not_connected__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a1 G hnot
  obtain ⟨K, hGK, hKG, hK⟩ :=
    WilliamsonShmoys.planar_add_edge_between_unreachable_vertices__p2m_b0b687f8_4cc8_496c_af1a_60542cca02f0_a1 G hG u v huv
  have hEq := hmax K hGK hK
  exact hKG hEq