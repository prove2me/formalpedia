-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_for_edge_maximal_graph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:40:52.90157+00:00
-- url     : https://prove2.me/submissions/880b853c-a0dc-4269-9c16-9d2ebc16f4e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_c61b3391
import Theorems.Thm_WilliamsonShmoys_edge_count_le_of_edge_maximal_planar_c61b3391

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph_c61b3391 G hG
  have hbound := WilliamsonShmoys.edge_count_le_of_edge_maximal_planar_c61b3391 H hV hH hmax
  have hsubset : G.edgeSet ⊆ H.edgeSet :=
    SimpleGraph.edgeSet_subset_edgeSet.mpr hGH
  exact (Set.ncard_mono hsubset).trans hbound