-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_edgeSet_ncard_le_of_connected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:00:31.878698+00:00
-- url     : https://prove2.me/submissions/f545aad1-c5c4-4cfa-8bb9-69e4879ab938
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_face_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hCard : 3 <= Fintype.card V)
    (hConnected : J.Connected) :
    J.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler, hFace⟩ :=
    WilliamsonShmoys.planar_drawingOn_face_count J hDraw hCard hConnected
  omega