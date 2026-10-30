-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulation_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:40:17.575209+00:00
-- url     : https://prove2.me/submissions/5b0a6db4-1a69-46a2-9f1a-d7d12bd07f50

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph_94348bb4_0897_41cb_a4e2_91f9fb7adb36
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_94348bb4_0897_41cb_a4e2_91f9fb7adb36

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    ∃ M : SimpleGraph V, G <= M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 = M.edgeSet.ncard := by
  obtain ⟨M, hGM, hM, hmax⟩ :=
    WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph_94348bb4_0897_41cb_a4e2_91f9fb7adb36 G hG
  refine ⟨M, hGM, hM, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_edge_count_94348bb4_0897_41cb_a4e2_91f9fb7adb36 M hM hV hmax