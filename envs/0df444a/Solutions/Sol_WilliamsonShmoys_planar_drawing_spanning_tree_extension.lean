-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_spanning_tree_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:20:24.559026+00:00
-- url     : https://prove2.me/submissions/9d6d40e7-34a2-4e61-b071-120fc0aedc8e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph
import Theorems.Thm_WilliamsonShmoys_connected_graph_spanning_subgraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H T : SimpleGraph V,
      (∀ u v, L.Adj u v → H.Adj u v) ∧
      T.Connected ∧
      (∀ u v, T.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hLH, hH, hPlanar, hEdges⟩ :=
    WilliamsonShmoys.connected_planar_supergraph L hV hL
  obtain ⟨T, hT, hTH⟩ :=
    WilliamsonShmoys.connected_graph_spanning_subgraph H hH
  exact ⟨H, T, hLH, hT, hTH, hPlanar, hEdges⟩