-- Prove2me | solution 2 for WilliamsonShmoys.connect_planar_components__p2m_aa8f027a_93b4_4926_a309_4c6509e6e203_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:17:51.895262+00:00
-- url     : https://prove2.me/submissions/df3386c6-30c6-42c0-8f7e-83cc5cd0a243

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_e750187a_6814_42ad_9805_f7d2cd135631_a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, L.edgeSet.ncard ≤ H.edgeSet.ncard ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H :=
  WilliamsonShmoys.planar_drawing_connected_extension__p2m_e750187a_6814_42ad_9805_f7d2cd135631_a2 L hDraw hV
