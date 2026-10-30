-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_simple_graph_edge_bound_euler
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:57:42.8601+00:00
-- url     : https://prove2.me/submissions/21eda0a9-45d3-4f19-b63c-faf1aba34c0b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_simple_graph_triangulation
import Theorems.Thm_WilliamsonShmoys_simpleGraph_edgeSet_ncard_mono

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : ∀ u v, Relation.ReflTransGen G.Adj u v)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, htri⟩ :=
    WilliamsonShmoys.connected_planar_simple_graph_triangulation G hG hconn hV
  calc
    G.edgeSet.ncard ≤ H.edgeSet.ncard :=
      WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono G H hGH
    _ = 3 * Fintype.card V - 6 := htri