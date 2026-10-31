-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_931a7134_e35c_41e8_a8b3_e1bad0c19dd8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:04:24.499383+00:00
-- url     : https://prove2.me/submissions/1d97322b-1d7f-4961-9b5a-55d89f32e881

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_edge_count__p2m_128ccb5d_2869_4813_8833_a7ab44ab4b11_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ H : SimpleGraph V, W ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = W)
    (hV : 3 ≤ Fintype.card V) :
    W.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hWH, hHplanar, hHcount⟩ :=
    WilliamsonShmoys.maximal_planar_extension_edge_count__p2m_128ccb5d_2869_4813_8833_a7ab44ab4b11_a1
      W hW hV
  have hEq : H = W := hmax H hWH hHplanar
  rw [hEq] at hHcount
  exact hHcount