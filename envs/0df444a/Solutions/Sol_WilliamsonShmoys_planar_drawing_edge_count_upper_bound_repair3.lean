-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound_repair3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:10:45.290795+00:00
-- url     : https://prove2.me/submissions/d9e12a90-b3ed-4b53-aca6-b5ddb4aa6f6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_repair3
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count_upper_bound_repair3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨S, hTS, hS, hconn, hmono⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension_repair3 T hT hCard
  have hbound :=
    WilliamsonShmoys.connected_planar_drawing_edge_count_upper_bound_repair3
      S hS hconn hCard
  omega