-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph_nontrivial_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:25:38.480309+00:00
-- url     : https://prove2.me/submissions/41539030-555c-424c-9891-eb58ffe32620
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_extension_reaches_connected
import Theorems.Thm_WilliamsonShmoys_disconnected_drawing_has_strict_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, W ≤ K ∧ K.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn K := by
  exact WilliamsonShmoys.finite_extension_reaches_connected
    (P := WilliamsonShmoys.HasPlanarDrawingOn) W hdraw
    (fun G hWG hG hDisconnected =>
      WilliamsonShmoys.disconnected_drawing_has_strict_extension
        G hG hV hDisconnected)