-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extends_to_maximal_planar__p2m_3eaf26d3_b02e_4c77_b998_3e9af8fb07e7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:42:29.863331+00:00
-- url     : https://prove2.me/submissions/f77acb67-0667-4e14-add1-3a3a48866870

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_inclusion_maximal_planar_extension__p2m_e7bfefe9_c4cd_4b0d_b2f1_de0e94ecd613_a2
import Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_graph_has_triangulation_edge_count__p2m_e7bfefe9_c4cd_4b0d_b2f1_de0e94ecd613_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      M.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hMH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_inclusion_maximal_planar_extension__p2m_e7bfefe9_c4cd_4b0d_b2f1_de0e94ecd613_a2 M hM
  refine ⟨H, hMH, hH, ?_⟩
  exact WilliamsonShmoys.inclusion_maximal_planar_graph_has_triangulation_edge_count__p2m_e7bfefe9_c4cd_4b0d_b2f1_de0e94ecd613_a2 H hH hCard hmax