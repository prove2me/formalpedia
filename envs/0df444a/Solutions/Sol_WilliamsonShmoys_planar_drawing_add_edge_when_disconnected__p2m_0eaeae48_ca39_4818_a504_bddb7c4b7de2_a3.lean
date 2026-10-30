-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_edge_when_disconnected__p2m_0eaeae48_ca39_4818_a504_bddb7c4b7de2_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T08:46:55.345908+00:00
-- url     : https://prove2.me/submissions/3b0913e8-b7e9-4548-b83d-30d83d189de8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_vertices_not_connected__p2m_f3cc24e6_d1b8_4aae_a4a3_597bfb5e0269_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_components__p2m_f3cc24e6_d1b8_4aae_a4a3_597bfb5e0269_a2
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hDisc : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ G.edgeSet ⊂ H.edgeSet := by
  obtain ⟨u, v, huv⟩ := WilliamsonShmoys.disconnected_vertices_not_connected__p2m_f3cc24e6_d1b8_4aae_a4a3_597bfb5e0269_a2 G hDisc
  exact WilliamsonShmoys.planar_drawing_add_edge_between_components__p2m_f3cc24e6_d1b8_4aae_a4a3_597bfb5e0269_a2 G hG huv