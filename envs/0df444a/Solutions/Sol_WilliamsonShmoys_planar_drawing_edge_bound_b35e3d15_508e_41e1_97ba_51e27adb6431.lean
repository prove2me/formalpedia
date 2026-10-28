-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_b35e3d15_508e_41e1_97ba_51e27adb6431
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:33:41.057405+00:00
-- url     : https://prove2.me/submissions/3d3f3697-4252-4a97-b374-8e14be7b80b8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_connected_b35e3d15_508e_41e1_97ba_51e27adb6431
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_of_connected_bound_b35e3d15_508e_41e1_97ba_51e27adb6431

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  exact WilliamsonShmoys.planar_drawing_edge_bound_of_connected_bound_b35e3d15_508e_41e1_97ba_51e27adb6431
    (H := H) (hV := hV) (hH := hH)
    (hconnected := by
      intro W hW hOrder K hK hKconn hKplanar
      exact WilliamsonShmoys.planar_drawing_edge_bound_connected_b35e3d15_508e_41e1_97ba_51e27adb6431
        (H := K) (hV := hK) (hconn := hKconn) (hH := hKplanar))