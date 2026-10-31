-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_517acab8_1dff_430a_88ba_b65381dc6f37_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:31:55.627982+00:00
-- url     : https://prove2.me/submissions/014c9dcf-f0b6-42af-ad63-abe9e5bff725
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_from_single_edge_step__p2m_54a1693d_5f6f_41b0_b799_793fe1e71489_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_single_edge_extension__p2m_54a1693d_5f6f_41b0_b799_793fe1e71489_a2

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, Z ≤ H ∧ H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  apply WilliamsonShmoys.planar_drawing_connected_augmentation_from_single_edge_step__p2m_54a1693d_5f6f_41b0_b799_793fe1e71489_a2
    Z hZ hV
  intro G hG hDisconnected
  exact WilliamsonShmoys.planar_drawing_single_edge_extension__p2m_54a1693d_5f6f_41b0_b799_793fe1e71489_a2
    G hG hDisconnected