-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_add_edge_when_disconnected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:07:17.771044+00:00
-- url     : https://prove2.me/submissions/a7749d57-f606-41dc-b95b-7393f9bec765
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_separated_nonadjacent_vertices
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_separated_vertices

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ H.Connected) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        H.edgeSet.ncard < K.edgeSet.ncard := by
  obtain ⟨u, v, huv, hnotAdj, hseparated⟩ :=
    WilliamsonShmoys.exists_separated_nonadjacent_vertices
      H hCard hNotConnected
  exact WilliamsonShmoys.planar_add_edge_between_separated_vertices
    H u v hseparated hHdraw