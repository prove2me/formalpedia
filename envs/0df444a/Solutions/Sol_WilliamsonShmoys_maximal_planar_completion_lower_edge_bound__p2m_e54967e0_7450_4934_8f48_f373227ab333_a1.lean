-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_completion_lower_edge_bound__p2m_e54967e0_7450_4934_8f48_f373227ab333_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:22:04.457189+00:00
-- url     : https://prove2.me/submissions/91c541d3-9e50-42b3-bfd2-4a8d79c4846a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_dense_completion__p2m_a1bc3295_288e_4dac_b293_e5c76a636381_a1

set_option autoImplicit false

open SimpleGraph
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hMax : forall N : SimpleGraph V, L <= N -> WilliamsonShmoys.HasPlanarDrawingOn N -> N <= L) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by
  obtain ⟨N, hLN, hN, hDense⟩ :=
    WilliamsonShmoys.planar_graph_has_dense_completion__p2m_a1bc3295_288e_4dac_b293_e5c76a636381_a1
      L hL hV
  have hNL : N <= L := hMax N hLN hN
  have hEdges : N.edgeSet ⊆ L.edgeSet := SimpleGraph.edgeSet_mono hNL
  have hCard : N.edgeSet.ncard <= L.edgeSet.ncard := Set.ncard_mono hEdges
  omega