-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_upper_bound_3fe6515b_8335_4a72_a208_f1a2ec6f6eaf
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:11:06.767903+00:00
-- url     : https://prove2.me/submissions/266d0652-a4e1-45ea-93a3-7d4987ad977c

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_large_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) : H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨K, hsub, hKconnected, hKplanar⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph_large_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd H hplanar hV
  exact le_trans (Set.ncard_mono hsub)
    (WilliamsonShmoys.connected_planar_edge_count_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd K hKconnected hKplanar hV)