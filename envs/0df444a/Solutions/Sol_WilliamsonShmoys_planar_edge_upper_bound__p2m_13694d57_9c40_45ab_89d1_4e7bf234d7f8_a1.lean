-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_13694d57_9c40_45ab_89d1_4e7bf234d7f8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:18:32.105047+00:00
-- url     : https://prove2.me/submissions/b3862202-cec8-459b-b262-1ffcd8643c7c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_upper_bound__p2m_c769ec5a_3e49_48b5_92c4_83cb5745da0c_a1
import Theorems.Thm_WilliamsonShmoys_planar_connected_augmentation__p2m_c769ec5a_3e49_48b5_92c4_83cb5745da0c_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨K, hEdges, hPlanar, hConnected⟩ :=
    WilliamsonShmoys.planar_connected_augmentation__p2m_c769ec5a_3e49_48b5_92c4_83cb5745da0c_a1
      H hH hV
  have hBound :=
    WilliamsonShmoys.planar_connected_edge_upper_bound__p2m_c769ec5a_3e49_48b5_92c4_83cb5745da0c_a1
      K hPlanar hConnected hV
  omega