-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_augmentation_edge_bound_93cad1d3_6631_4871_91db_d5199271705a
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T01:52:40.898824+00:00
-- url     : https://prove2.me/submissions/b6410ebe-b83b-40e1-bb7a-f5abc89d3cb0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_augmentation_for_edge_bound__p2m_1016eb9f_955e_4666_8793_89a9a11ff9b9_a5
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_bound__p2m_1016eb9f_955e_4666_8793_89a9a11ff9b9_a5

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    exists L : SimpleGraph V,
      K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        3 * Fintype.card V <= L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_augmentation_for_edge_bound__p2m_1016eb9f_955e_4666_8793_89a9a11ff9b9_a5 K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_drawable_graph_edge_bound__p2m_1016eb9f_955e_4666_8793_89a9a11ff9b9_a5 L hV hL hmax⟩