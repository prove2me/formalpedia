-- Prove2me | solution 3 for WilliamsonShmoys.disconnected_planar_graph_has_strict_planar_extension_of_three_vertices__p2m_76da28cf_203d_4767_b5f5_69763f85c611_a2
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:22:20.495246+00:00
-- url     : https://prove2.me/submissions/678e7840-9ed0-4a09-ba56-f6256cc2af74

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hdis : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G < H ∧ HasPlanarDrawingOn H := by
  obtain ⟨J, hGJ, hne, hJ⟩ :=
    WilliamsonShmoys.planar_edge_extension_of_disconnected_drawing G hG hV hdis
  exact ⟨J, lt_of_le_of_ne hGJ (Ne.symm hne), hJ⟩
