-- Prove2me | solution 1 for WilliamsonShmoys.planar_subgraph_edge_bound_of_connected_planar_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:55:34.64847+00:00
-- url     : https://prove2.me/submissions/c7b473a1-5c4b-4b83-98a3-1a5c132d5f54

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_subgraph_edge_count_le
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_le

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G H : SimpleGraph V)
    (hGH : G ≤ H) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have h_edges : G.edgeSet.ncard ≤ H.edgeSet.ncard :=
    WilliamsonShmoys.subgraph_edge_count_le G H hGH
  have h_planar : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.connected_planar_edge_count_le H hdraw hconn hV
  omega