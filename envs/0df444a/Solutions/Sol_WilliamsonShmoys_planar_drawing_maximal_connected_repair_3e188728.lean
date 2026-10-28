-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_connected_repair_3e188728
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:53:52.440679+00:00
-- url     : https://prove2.me/submissions/d81483a4-dd8f-4863-bed3-ebf2485fc9bd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_of_not_connected

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 0 < Fintype.card V)
    (hMaximal : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.Connected := by
  by_contra hConnected
  obtain ⟨K, hHK, hneq, hK⟩ :=
    WilliamsonShmoys.planar_drawing_add_edge_of_not_connected H hH hV hConnected
  exact hneq (hMaximal K hHK hK)