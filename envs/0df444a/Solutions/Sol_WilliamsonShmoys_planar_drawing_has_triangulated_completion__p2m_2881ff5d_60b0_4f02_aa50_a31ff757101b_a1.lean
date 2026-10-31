-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_completion__p2m_2881ff5d_60b0_4f02_aa50_a31ff757101b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:49:46.12521+00:00
-- url     : https://prove2.me/submissions/e3842ef4-ed6a-4c51-9daf-08e41b58d213

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_completion__p2m_92efd15a_1c37_4034_81a1_98dbd8d1208a_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_has_triangulation_count__p2m_92efd15a_1c37_4034_81a1_98dbd8d1208a_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        3 * Fintype.card V - 6 = K.edgeSet.ncard := by
  obtain ⟨K, hNK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_completion__p2m_92efd15a_1c37_4034_81a1_98dbd8d1208a_a1 N hN
  exact ⟨K, hNK, hK,
    WilliamsonShmoys.edge_maximal_planar_graph_has_triangulation_count__p2m_92efd15a_1c37_4034_81a1_98dbd8d1208a_a1 K hV hK hmax⟩