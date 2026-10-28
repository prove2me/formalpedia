-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_afa305d5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:34:34.317418+00:00
-- url     : https://prove2.me/submissions/f28065ef-0b0f-4d24-b4ab-30702dddb504
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_triangulated_extension

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall J : SimpleGraph V, H <= J ->
      WilliamsonShmoys.HasPlanarDrawingOn J -> J = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKDraw, hKCount⟩ :=
    WilliamsonShmoys.planar_drawingOn_triangulated_extension H hDraw hCard
  have hKH : K = H := hMax K hHK hKDraw
  simpa [hKH] using hKCount