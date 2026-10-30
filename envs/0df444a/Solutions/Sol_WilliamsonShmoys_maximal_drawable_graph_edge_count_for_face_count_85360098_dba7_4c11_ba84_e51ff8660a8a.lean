-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_for_face_count_85360098_dba7_4c11_ba84_e51ff8660a8a
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:15:50.700326+00:00
-- url     : https://prove2.me/submissions/0d8735b7-4b2a-45b3-b122-3e19734e47a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_c9f2f72f_e500_46c8_ab0e_7bffe07c2b59_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_c9f2f72f_e500_46c8_ab0e_7bffe07c2b59_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : ∀ T : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn T →
      R ≤ T → T = R)
    (hCard : 3 ≤ Fintype.card V) :
    R.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c9f2f72f_e500_46c8_ab0e_7bffe07c2b59_a1 R hR hCard
  have hLower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c9f2f72f_e500_46c8_ab0e_7bffe07c2b59_a1 R hR hmax hCard
  omega