-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_euler_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T09:44:12.392286+00:00
-- url     : https://prove2.me/submissions/0ba88bb8-f96a-4c02-955d-b67d3de8ca23
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_v2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hsub, hcard, hconn, hplanar⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation_v2 K hK
  have hbound :=
    WilliamsonShmoys.connected_planar_drawing_edge_bound_v2 H hV hconn hplanar
  omega