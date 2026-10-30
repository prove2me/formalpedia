-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_fixed_vertex_0e6cbe52_e2e3_41cf_80dc_2d34dacc7938
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:35:16.686311+00:00
-- url     : https://prove2.me/submissions/e8e77542-3bb4-468d-907d-b67626794a0f

import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_on_fixed_vertices
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_via_euler_c27addfb_131a_4167_b7de_c130c93bb2da

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V,
      U ≤ W ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      3 * Fintype.card V = W.edgeSet.ncard + 6 := by
  obtain ⟨W, hUW, hW, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_on_fixed_vertices U hV hU
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count_via_euler_c27addfb_131a_4167_b7de_c130c93bb2da
      W hV hW hmax
  exact ⟨W, hUW, hW, hcount⟩