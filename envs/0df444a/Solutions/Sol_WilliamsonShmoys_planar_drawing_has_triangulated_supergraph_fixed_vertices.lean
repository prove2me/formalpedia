-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulated_supergraph_fixed_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:15:18.507463+00:00
-- url     : https://prove2.me/submissions/d2e8b503-d9a9-456e-9cfb-44fd159cd4c7

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_extension_for_fixed_vertices_38271ead_fcb7_486e_b3a1_3bd65c5883ef
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_edge_count_38271ead_fcb7_486e_b3a1_3bd65c5883ef

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      N ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (M.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨M, hNM, hM, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_edge_maximal_extension_for_fixed_vertices_38271ead_fcb7_486e_b3a1_3bd65c5883ef N hN
  refine ⟨M, hNM, hM, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count_38271ead_fcb7_486e_b3a1_3bd65c5883ef M hM hCard hMax