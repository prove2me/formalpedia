-- Prove2me | solution 1 for WilliamsonShmoys.planar_sparse_graph_has_planar_edge_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:39:55.1169+00:00
-- url     : https://prove2.me/submissions/d5f3d99a-f739-4ad0-b320-bd97377b3405

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_sparse_graph_has_maximal_planar_supergraph_2e173d6b
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_2e173d6b
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hsparse : L.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M ≠ L := by
  obtain ⟨M, hLM, hM, hmax⟩ :=
    WilliamsonShmoys.planar_sparse_graph_has_maximal_planar_supergraph_2e173d6b L hL
  have hcount := WilliamsonShmoys.maximal_planar_graph_edge_count_2e173d6b M hV hM hmax
  refine ⟨M, hLM, hM, ?_⟩
  intro hEq
  subst M
  omega