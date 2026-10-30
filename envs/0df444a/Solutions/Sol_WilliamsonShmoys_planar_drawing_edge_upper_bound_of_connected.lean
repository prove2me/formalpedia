-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound_of_connected
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:19:46.108554+00:00
-- url     : https://prove2.me/submissions/ab93900b-bf28-4476-b8bc-5726a356c81c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_exists_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planarDrawingOn_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : ∀ u v : V, Nonempty (G.Walk u v)) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hHconn, hmax, hcard⟩ :=
    WilliamsonShmoys.planarDrawingOn_exists_maximal_supergraph G hG hV hconn
  have hcount := WilliamsonShmoys.maximal_planarDrawingOn_edge_count H hH hV hHconn hmax
  exact le_trans hcard (le_of_eq hcount)