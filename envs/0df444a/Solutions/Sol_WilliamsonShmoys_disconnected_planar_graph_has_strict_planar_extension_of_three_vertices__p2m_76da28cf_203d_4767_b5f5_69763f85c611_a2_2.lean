-- Prove2me | solution 2 for WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_extension_of_three_vertices__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:05:46.580426+00:00
-- url     : https://prove2.me/submissions/37370bdc-1589-4ae0-a44e-a12e7c21df87
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_vertices_across_components_with_nonempty__p2m_293787da_4b73_4bb8_b4f9_49ac7bd93d8f_a2
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_components__p2m_293787da_4b73_4bb8_b4f9_49ac7bd93d8f_a1
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hdis : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G < H ∧ HasPlanarDrawingOn H := by
  obtain ⟨u, v, huv, hnot⟩ :=
    WilliamsonShmoys.disconnected_vertices_across_components_with_nonempty__p2m_293787da_4b73_4bb8_b4f9_49ac7bd93d8f_a2
      G hV hdis
  obtain ⟨H, hstrict, hadj, hplanar⟩ :=
    WilliamsonShmoys.planar_add_edge_between_components__p2m_293787da_4b73_4bb8_b4f9_49ac7bd93d8f_a1
      G u v hG huv hnot
  exact ⟨H, hstrict, hplanar⟩