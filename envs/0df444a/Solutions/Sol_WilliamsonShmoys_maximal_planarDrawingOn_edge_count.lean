-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planarDrawingOn_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:23:04.795674+00:00
-- url     : https://prove2.me/submissions/aa157aa8-87f3-4a2a-be47-267cebd68985

import Theorems.Thm_WilliamsonShmoys_planar_simpleGraph_edge_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planarDrawingOn_edge_lower_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : ∀ u v : V, Nonempty (G.Walk u v))
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.planar_simpleGraph_edge_bound G hG hV hconn
  have hlower := WilliamsonShmoys.maximal_planarDrawingOn_edge_lower_bound
    G hG hV hconn hmax
  omega