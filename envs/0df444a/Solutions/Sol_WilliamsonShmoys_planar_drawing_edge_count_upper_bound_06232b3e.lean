-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound_06232b3e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:14:30.213892+00:00
-- url     : https://prove2.me/submissions/2716f2c8-b4a7-4e78-a2e1-60f8d5a8f118
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_06232b3e__p2m_2a9dccf6_668c_4d19_9019_ad95792f6898_a3
import Theorems.Thm_WilliamsonShmoys_planar_connected_drawing_edge_count_upper_bound_06232b3e__p2m_2a9dccf6_668c_4d19_9019_ad95792f6898_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, hLK, hKConnected, hKDrawing, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation_06232b3e__p2m_2a9dccf6_668c_4d19_9019_ad95792f6898_a3 L hL hCard
  exact le_trans hCount
    (WilliamsonShmoys.planar_connected_drawing_edge_count_upper_bound_06232b3e__p2m_2a9dccf6_668c_4d19_9019_ad95792f6898_a3
      K hKConnected hKDrawing hCard)