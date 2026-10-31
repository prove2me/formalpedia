-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_efe3e864_4fbd_4f0b_a1f2_70ba02623cb8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:13:54.567828+00:00
-- url     : https://prove2.me/submissions/9c7c0666-1512-4d6e-b262-bbb362ca19d4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_e54811a8_cc12_4b66_a567_2bf19301ebf6_a1
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_lower_bound__p2m_e54811a8_cc12_4b66_a567_2bf19301ebf6_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hUpper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_e54811a8_cc12_4b66_a567_2bf19301ebf6_a1
    K hK hV
  obtain ⟨L, hKL, hL, hLower⟩ :=
    WilliamsonShmoys.planar_supergraph_lower_bound__p2m_e54811a8_cc12_4b66_a567_2bf19301ebf6_a1
      K hK hV
  have hLK := hmax L hKL hL
  rw [hLK] at hLower
  exact Nat.le_antisymm hUpper hLower