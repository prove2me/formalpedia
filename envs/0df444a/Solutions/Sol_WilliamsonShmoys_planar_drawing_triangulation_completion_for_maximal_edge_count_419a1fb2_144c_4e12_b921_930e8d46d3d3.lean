-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion_for_maximal_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:31:08.171555+00:00
-- url     : https://prove2.me/submissions/b68f1a0d-8c74-4023-be99-6c130babf4a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_drawable_supergraph_419a1fb2_144c_4e12_b921_930e8d46d3d3
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_planar_graph_has_exact_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨K, hNK, hK, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_drawable_supergraph_419a1fb2_144c_4e12_b921_930e8d46d3d3
      N hN
  exact ⟨K, hNK, hK,
    WilliamsonShmoys.maximal_drawable_planar_graph_has_exact_edge_count_419a1fb2_144c_4e12_b921_930e8d46d3d3
      K hK hCard hMax⟩