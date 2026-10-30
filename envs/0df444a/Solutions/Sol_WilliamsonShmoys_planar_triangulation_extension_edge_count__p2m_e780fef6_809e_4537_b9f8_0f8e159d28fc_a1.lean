-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_e780fef6_809e_4537_b9f8_0f8e159d28fc_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:05:58.937054+00:00
-- url     : https://prove2.me/submissions/ec7145bd-1c87-4bc5-9eb5-f5e4a7bc2cee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_70a8b6e0_c40a_44e8_9147_f9396a2e926b_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_70a8b6e0_c40a_44e8_9147_f9396a2e926b_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hV : LE.le 3 (Fintype.card V)) :
    Exists fun H : SimpleGraph V =>
      And (LE.le G H) (And (HasPlanarDrawingOn H)
        (H.edgeSet.ncard + 6 = 3 * Fintype.card V)) := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_70a8b6e0_c40a_44e8_9147_f9396a2e926b_a2
      G hG
  refine ⟨H, hGH, hH, ?_⟩
  exact
    (WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_70a8b6e0_c40a_44e8_9147_f9396a2e926b_a2
      H hH hV hmax).symm