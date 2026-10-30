-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_extension_of_disconnected_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:16:03.932933+00:00
-- url     : https://prove2.me/submissions/0f319a9b-1749-4a8c-89f4-d5592d6ae107

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_drawing_has_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V)
    (hDisconnected : ¬ H.Connected) :
    ∃ J : SimpleGraph V, H <= J ∧ J ≠ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn J := by
  obtain ⟨J, hHJ, hJ, hMax⟩ :=
    WilliamsonShmoys.disconnected_drawing_has_maximal_supergraph H hDraw
  have hConn : J.Connected :=
    WilliamsonShmoys.maximal_planar_drawingOn_connected J hJ hMax hCard
  refine ⟨J, hHJ, ?_, hJ⟩
  intro hEq
  subst J
  exact hDisconnected hConn