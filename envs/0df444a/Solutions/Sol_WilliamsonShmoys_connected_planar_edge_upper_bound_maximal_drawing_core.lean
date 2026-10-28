-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_upper_bound_maximal_drawing_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:24:49.839787+00:00
-- url     : https://prove2.me/submissions/323c8429-1f28-4a24-8b31-ea6cc5eaa1c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_b35e3d15_508e_41e1_97ba_51e27adb6431

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  exact WilliamsonShmoys.planar_drawing_edge_bound_b35e3d15_508e_41e1_97ba_51e27adb6431 H hV hH