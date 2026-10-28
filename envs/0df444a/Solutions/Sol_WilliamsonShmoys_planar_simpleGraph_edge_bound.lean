-- Prove2me | solution 1 for WilliamsonShmoys.planar_simpleGraph_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:27:48.977094+00:00
-- url     : https://prove2.me/submissions/252ed021-b584-49c2-8f8d-b5a22f100061
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : ∀ u v : V, Nonempty (G.Walk u v)) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hsub, hHplanar, hcard_le, hHcard⟩ :=
    WilliamsonShmoys.exists_triangulated_planar_supergraph G hG hV hconn
  exact le_trans hcard_le (le_of_eq hHcard)