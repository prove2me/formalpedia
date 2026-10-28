-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_bound_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:15:19.365353+00:00
-- url     : https://prove2.me/submissions/aa75715a-b3c4-422e-a771-e9531aa67c1c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_counts_v2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hConnected : L.Connected)
    (hCard : 3 <= Fintype.card V) :
    L.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaceDegree⟩ :=
    WilliamsonShmoys.connected_planar_drawing_euler_counts_v2
      L hLdraw hConnected hCard
  omega