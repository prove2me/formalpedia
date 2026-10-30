-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulated_supergraph_for_419a1fb2_144c_4e12_b921_930e8d46d3d3_planar_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:08:48.804174+00:00
-- url     : https://prove2.me/submissions/3cf4f11b-51a2-46fe-8fa0-1b8a2c7283a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_supergraph_same_vertex_completion_7e0405ab
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_euler_7e0405ab

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hKH, hHplanar, hmono, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_planar_supergraph_same_vertex_completion_7e0405ab
      (K := K) hK
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count_euler_7e0405ab
      (H := H) hHplanar hCard hmax
  exact ⟨H, hKH, hHplanar, hmono, hcount⟩