-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulated_extension_edge_count__p2m_55ffc515_2d9b_4bf9_8fab_2747393ddd23_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:14:40.676654+00:00
-- url     : https://prove2.me/submissions/f5519056-0d10-44cf-a4ec-10e41da7272c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_drawable_extension__p2m_df568397_14d2_4b43_b482_47a2ce432eea_a2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_planar_edge_count__p2m_df568397_14d2_4b43_b482_47a2ce432eea_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_graph_has_maximal_drawable_extension__p2m_df568397_14d2_4b43_b482_47a2ce432eea_a2
      H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_drawable_graph_has_planar_edge_count__p2m_df568397_14d2_4b43_b482_47a2ce432eea_a2
      K hCard hK hmax⟩
