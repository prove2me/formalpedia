-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:21:15.421285+00:00
-- url     : https://prove2.me/submissions/2e8488c0-657c-4ce4-8498-61f794e76ecc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge
import Theorems.Thm_WilliamsonShmoys_connected_supergraph_of_planar_bridge_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ u v : V, Nonempty (H.Walk u v)) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  exact WilliamsonShmoys.connected_supergraph_of_planar_bridge_extension
    G hG hV (by
      intro K hK hDisconnected
      exact WilliamsonShmoys.planar_drawing_add_bridge K hK hDisconnected)