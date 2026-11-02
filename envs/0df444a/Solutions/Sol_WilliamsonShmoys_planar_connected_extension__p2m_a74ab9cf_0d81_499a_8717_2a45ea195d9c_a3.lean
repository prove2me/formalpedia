-- Prove2me | solution 1 for WilliamsonShmoys_planar_connected_extension__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:37:16.076338+00:00
-- url     : https://prove2.me/submissions/68f3915e-aae0-4b0c-81b8-cf4f19a4121d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_f305e987_8fa4_48f1_bb88_04ada6b91b35_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_connected__p2m_f305e987_8fa4_48f1_bb88_04ada6b91b35_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ G : SimpleGraph V, H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G ∧ G.Connected := by
  obtain ⟨G, hHG, hG, hmax⟩ :=
    WilliamsonShmoys_planar_drawing_maximal_extension__p2m_f305e987_8fa4_48f1_bb88_04ada6b91b35_a2 H hH
  exact ⟨G, hHG, hG,
    WilliamsonShmoys_maximal_planar_graph_connected__p2m_f305e987_8fa4_48f1_bb88_04ada6b91b35_a2 G hcard hG hmax⟩