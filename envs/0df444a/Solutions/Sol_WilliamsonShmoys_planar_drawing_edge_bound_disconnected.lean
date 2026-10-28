-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_disconnected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:20:25.712911+00:00
-- url     : https://prove2.me/submissions/1c772484-477a-4506-a065-069dcb94205b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_spanning_augmentation
import Theorems.Thm_WilliamsonShmoys_planar_subgraph_edge_bound_of_connected_planar_supergraph

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn T) (hnotconn : ¬ T.Connected)
    (hV : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hTH, hHconn, hHdraw⟩ :=
    WilliamsonShmoys.planar_connected_spanning_augmentation T hdraw hnotconn
  exact WilliamsonShmoys.planar_subgraph_edge_bound_of_connected_planar_supergraph
    T H hTH hHdraw hHconn hV