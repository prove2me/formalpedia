-- Prove2me | solution 1 for WilliamsonShmoys.planar_augmentation_across_components__p2m_cc5cc3f2_db05_4ace_b001_4997052bea6e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:36:24.056419+00:00
-- url     : https://prove2.me/submissions/a29c7058-f059-4af5-b058-a96de3b028c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_39e1387e_c6b4_4e32_ad1b_235228b03693_a4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_connected__p2m_39e1387e_c6b4_4e32_ad1b_235228b03693_a4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) {u v : V}
    (huv : u ≠ v) (hnotReachable : ¬ H.Reachable u v) :
    ∃ J : SimpleGraph V, H ≤ J ∧ HasPlanarDrawingOn J ∧ ¬ J ≤ H := by
  obtain ⟨L, hHL, hL, hMax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_39e1387e_c6b4_4e32_ad1b_235228b03693_a4 H hH
  have hconn := WilliamsonShmoys.maximal_planar_graph_connected__p2m_39e1387e_c6b4_4e32_ad1b_235228b03693_a4 L hL hMax huv
  by_cases hLH : L ≤ H
  · have hHL' : H ≤ L := hMax H hLH hH
    have heq : L = H := le_antisymm hLH hHL'
    rw [heq] at hconn
    exact False.elim (hnotReachable hconn)
  · exact ⟨L, hHL, hL, hLH⟩