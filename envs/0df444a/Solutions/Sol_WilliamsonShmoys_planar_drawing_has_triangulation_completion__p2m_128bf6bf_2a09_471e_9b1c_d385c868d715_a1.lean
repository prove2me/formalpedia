-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulation_completion__p2m_128bf6bf_2a09_471e_9b1c_d385c868d715_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T21:25:15.135386+00:00
-- url     : https://prove2.me/submissions/044bd7e1-9fad-42d9-ad94-0c24fb13d2ec

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_8c6a7d59_3d50_48bd_989b_b7738f5488ee_a3
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_8c6a7d59_3d50_48bd_989b_b7738f5488ee_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKdraw, hKmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_8c6a7d59_3d50_48bd_989b_b7738f5488ee_a3 H hH
  exact ⟨K, hHK, hKdraw,
    WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_8c6a7d59_3d50_48bd_989b_b7738f5488ee_a3 K hKdraw hCard hKmax⟩