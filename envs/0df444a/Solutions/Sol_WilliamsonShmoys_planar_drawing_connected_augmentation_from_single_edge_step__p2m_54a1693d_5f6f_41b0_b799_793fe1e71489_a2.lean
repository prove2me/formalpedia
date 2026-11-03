-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation_from_single_edge_step__p2m_54a1693d_5f6f_41b0_b799_793fe1e71489_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:32:26.488551+00:00
-- url     : https://prove2.me/submissions/5dbc7576-8cc9-42cf-8cc6-30fce9aedab6

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation__p2m_517acab8_1dff_430a_88ba_b65381dc6f37_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Z : SimpleGraph V) (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) (hV : 3 ≤ Fintype.card V) (hStep : ∀ (G : SimpleGraph V), WilliamsonShmoys.HasPlanarDrawingOn G → ¬ G.Connected → ∃ H : SimpleGraph V, G ≤ H ∧ ¬ H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ H : SimpleGraph V, Z ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H :=
  WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_517acab8_1dff_430a_88ba_b65381dc6f37_a1 Z hZ hV