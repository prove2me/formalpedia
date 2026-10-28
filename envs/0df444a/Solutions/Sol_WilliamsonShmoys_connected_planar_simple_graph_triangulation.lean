-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_simple_graph_triangulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:04:27.417187+00:00
-- url     : https://prove2.me/submissions/8a45f2b8-c1f6-418f-b5ac-90bbebd4d8db
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_simple_graph_triangulation_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_edge_count

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : ∀ u v, Relation.ReflTransGen G.Adj u v)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hHconn, hmax⟩ :=
    WilliamsonShmoys.connected_planar_simple_graph_triangulation_maximal_extension
      G hG hconn hV
  have hcount :=
    WilliamsonShmoys.maximal_planar_simple_graph_edge_count H hH hHconn hV hmax
  exact ⟨H, hGH, hH, hcount⟩