-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:48:45.729423+00:00
-- url     : https://prove2.me/submissions/1d49a867-3994-4cd1-a34d-7e8d6e41fc20

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_fixed_vertex_type
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_fixed_vertex_type

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      W.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hWH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_fixed_vertex_type W hW
  refine ⟨H, hWH, hH, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count_fixed_vertex_type H hH hV hmax