-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_connected_from_maximality_afa305d5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:34:06.310506+00:00
-- url     : https://prove2.me/submissions/2472e340-43ef-42d6-aa1d-0b409df4c69a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall J : SimpleGraph V, H <= J ->
      WilliamsonShmoys.HasPlanarDrawingOn J -> J = H) :
    H.Connected := by
  by_contra hConnected
  obtain ⟨J, hSub, hNe, hJDraw⟩ :=
    WilliamsonShmoys.planar_edge_extension_of_disconnected_drawing
      H hDraw hCard hConnected
  exact hNe (hMax J hSub hJDraw)