-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation_v3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:29:26.884232+00:00
-- url     : https://prove2.me/submissions/27fded20-b35a-4b47-bb48-5e0d836a6f5d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_single_edge_planar_drawing_extension
import Theorems.Thm_WilliamsonShmoys_connected_planar_augmentation_of_edge_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun H : SimpleGraph V =>
      (forall u v : V, K.Adj u v -> H.Adj u v) /\
      K.edgeSet.ncard <= H.edgeSet.ncard /\
      H.Connected /\
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  exact WilliamsonShmoys.connected_planar_augmentation_of_edge_extension K hV hK
    (fun G hV' hG hDisconnected =>
      WilliamsonShmoys.single_edge_planar_drawing_extension
        G hV' hG hDisconnected)