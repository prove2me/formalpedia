-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:08:22.77256+00:00
-- url     : https://prove2.me/submissions/8cb8f498-bdb7-46b2-9513-9e5c34a754ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_one_edge_augmentation__p2m_b6f7b032_7d17_4abc_a25e_6614208f3ad2_a1
import Theorems.Thm_WilliamsonShmoys_connected_supergraph_from_one_edge_augmentations__p2m_b6f7b032_7d17_4abc_a25e_6614208f3ad2_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  exact WilliamsonShmoys.connected_supergraph_from_one_edge_augmentations__p2m_b6f7b032_7d17_4abc_a25e_6614208f3ad2_a1
    (P := WilliamsonShmoys.HasPlanarDrawingOn)
    (fun G hG hnc =>
      WilliamsonShmoys.planar_drawing_one_edge_augmentation__p2m_b6f7b032_7d17_4abc_a25e_6614208f3ad2_a1
        G hG hnc)
    K hK