-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_simple_graph_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:13:17.685327+00:00
-- url     : https://prove2.me/submissions/7368da71-84db-463b-bdaf-cb9fe15fd64e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_edge_lower_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : ∀ u v, Relation.ReflTransGen H.Adj u v)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hu := WilliamsonShmoys.planar_simple_graph_edge_upper_bound
    H hH hconn hV
  have hl := WilliamsonShmoys.maximal_planar_simple_graph_edge_lower_bound
    H hH hconn hV hmax
  omega