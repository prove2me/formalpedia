-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_drawing_proper_extension_connectedification_retry3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:43:26.203995+00:00
-- url     : https://prove2.me/submissions/3864a57d-48d5-4e50-8654-6495394a1258

import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_of_disconnected_drawing

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hNotConnected : ¬ H.Connected) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      K ≠ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn K :=
  WilliamsonShmoys.planar_edge_extension_of_disconnected_drawing H hDraw hCard hNotConnected
