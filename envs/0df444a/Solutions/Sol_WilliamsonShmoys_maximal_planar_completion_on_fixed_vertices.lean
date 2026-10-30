-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_completion_on_fixed_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:04:33.430231+00:00
-- url     : https://prove2.me/submissions/33014b1a-5a2e-4d0c-b483-8f3b02410a04

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_fixed_vertices_5000a3d3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_fixed_vertices_5000a3d3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun X : SimpleGraph V =>
      G <= X /\ WilliamsonShmoys.HasPlanarDrawingOn X /\
      3 * Fintype.card V = X.edgeSet.ncard + 6 := by
  obtain ⟨X, hGX, hX, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal_fixed_vertices_5000a3d3 G hG
  exact ⟨X, hGX, hX,
    WilliamsonShmoys.maximal_planar_edge_count_fixed_vertices_5000a3d3 X hV hX hmax⟩