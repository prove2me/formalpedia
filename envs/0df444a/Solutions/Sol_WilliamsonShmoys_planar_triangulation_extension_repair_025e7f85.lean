-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_repair_025e7f85
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:47:26.780992+00:00
-- url     : https://prove2.me/submissions/007cbbb8-ebe6-4d08-9435-b7ed95ea3c10

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_repair_0d3f2800_82dc_4ab9_ba1d_464ebc548881
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_repair_0d3f2800_82dc_4ab9_ba1d_464ebc548881

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_repair_0d3f2800_82dc_4ab9_ba1d_464ebc548881 K hK
  refine ⟨L, hKL, hL, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_edge_count_repair_0d3f2800_82dc_4ab9_ba1d_464ebc548881 L hL hMax hCard