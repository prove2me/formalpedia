-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph_v3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:25:11.201158+00:00
-- url     : https://prove2.me/submissions/fc236be1-dd07-4e14-9d88-450670068d35
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_of_disconnected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_of_augmentable
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V,
      Y ≤ Z ∧
      Y.edgeSet.ncard ≤ Z.edgeSet.ncard ∧
      Z.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z := by
  exact WilliamsonShmoys.planar_drawing_connected_of_augmentable
    Y hV hY
    (fun X hX hn =>
      WilliamsonShmoys.planar_drawing_add_edge_of_disconnected X hV hX hn)