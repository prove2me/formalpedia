-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_completion__p2m_0ce4b12f_9c91_441c_b797_1286dedfdf8a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:22:06.143829+00:00
-- url     : https://prove2.me/submissions/120064b2-a8bf-482b-9e4c-cd6127a054eb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_deletion_closed__p2m_eee70f1a_2d3d_4378_a78c_629ec2b9156c_a1
import Theorems.Thm_finite_graph_maximal_extension__p2m_eee70f1a_2d3d_4378_a78c_629ec2b9156c_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet ⊆ K.edgeSet := by
  have hclosed : ∀ G F : SimpleGraph V,
      G.edgeSet ⊆ F.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn F →
      WilliamsonShmoys.HasPlanarDrawingOn G :=
    WilliamsonShmoys.planar_drawing_edge_deletion_closed__p2m_eee70f1a_2d3d_4378_a78c_629ec2b9156c_a1
  exact finite_graph_maximal_extension__p2m_eee70f1a_2d3d_4378_a78c_629ec2b9156c_a1
    WilliamsonShmoys.HasPlanarDrawingOn hclosed H hH