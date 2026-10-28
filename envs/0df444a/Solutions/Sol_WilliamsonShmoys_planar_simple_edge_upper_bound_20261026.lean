-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_upper_bound_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:31:01.828578+00:00
-- url     : https://prove2.me/submissions/10e1fa29-f4f0-4454-92a4-54cfada48499
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_connected_supergraph_20261026
import Theorems.Thm_WilliamsonShmoys_connected_planar_simple_edge_bound_20261026

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K', hKK', hconn, hK'⟩ :=
    WilliamsonShmoys.planar_drawingOn_connected_supergraph_20261026 K hK hV
  have hsub : K.edgeSet ⊆ K'.edgeSet := by
    exact (SimpleGraph.edgeSetEmbedding V).monotone hKK'
  exact le_trans (Set.ncard_mono hsub)
    (WilliamsonShmoys.connected_planar_simple_edge_bound_20261026 K' hconn hK' hV)