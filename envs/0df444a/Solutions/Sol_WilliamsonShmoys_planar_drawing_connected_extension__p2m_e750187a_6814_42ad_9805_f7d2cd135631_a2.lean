-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_e750187a_6814_42ad_9805_f7d2cd135631_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:13:29.851984+00:00
-- url     : https://prove2.me/submissions/905efcfe-2a92-4fe3-bfa7-763e7137c60d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_count__p2m_545b931b_2868_4b77_b00d_a5bf211937d5_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected__p2m_545b931b_2868_4b77_b00d_a5bf211937d5_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      L.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hContain, hCount, hHdraw, hMaximal⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count__p2m_545b931b_2868_4b77_b00d_a5bf211937d5_a1
      L hDraw
  have hConnected :=
    WilliamsonShmoys.maximal_planar_drawing_connected__p2m_545b931b_2868_4b77_b00d_a5bf211937d5_a1
      H hHdraw hCard hMaximal
  exact ⟨H, hCount, hConnected, hHdraw⟩