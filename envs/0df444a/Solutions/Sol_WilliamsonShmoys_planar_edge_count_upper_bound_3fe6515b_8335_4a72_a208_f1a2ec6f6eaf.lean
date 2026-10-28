-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_3fe6515b_8335_4a72_a208_f1a2ec6f6eaf
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:28:40.178383+00:00
-- url     : https://prove2.me/submissions/d6e58350-7e2f-46c9-a627-dd1a63da109b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) : H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨K, hsub, hKconnected, hKplanar⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd H hplanar
  exact le_trans (Set.ncard_mono hsub)
    (WilliamsonShmoys.connected_planar_edge_count_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd K hKconnected hKplanar hV)