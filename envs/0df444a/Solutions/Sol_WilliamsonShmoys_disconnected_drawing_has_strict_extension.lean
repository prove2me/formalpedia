-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_drawing_has_strict_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:46:12.730086+00:00
-- url     : https://prove2.me/submissions/6bebda04-480e-4f97-961f-46fe332ea14f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_drawing_has_strict_extension_separated_pair
import Theorems.Thm_WilliamsonShmoys_planar_strict_extension_of_separated_pair

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V, G < H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨u, v, huv, hseparate⟩ :=
    WilliamsonShmoys.disconnected_planar_drawing_has_strict_extension_separated_pair
      G hV hDisconnected
  exact WilliamsonShmoys.planar_strict_extension_of_separated_pair
    G hdraw huv hseparate