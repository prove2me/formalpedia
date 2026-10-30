-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_upper_bound__p2m_43e5ee36_822f_4bf9_b718_27a0868cee65_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:01:33.865328+00:00
-- url     : https://prove2.me/submissions/09e9daac-b945-4151-bafe-a6b7f203d2f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_with_three_vertices__p2m_425c8e2e_b612_4bb5_a030_cd4c3c162389_a2
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound__p2m_425c8e2e_b612_4bb5_a030_cd4c3c162389_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, hEdges, hConn, hKDraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension_with_three_vertices__p2m_425c8e2e_b612_4bb5_a030_cd4c3c162389_a2
      H hDraw hV
  exact le_trans (Set.ncard_mono hEdges)
    (WilliamsonShmoys.planar_connected_edge_bound__p2m_425c8e2e_b612_4bb5_a030_cd4c3c162389_a1
      K hKDraw hConn hV)