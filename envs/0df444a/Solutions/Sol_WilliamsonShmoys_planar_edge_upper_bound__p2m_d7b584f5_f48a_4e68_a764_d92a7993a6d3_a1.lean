-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_d7b584f5_f48a_4e68_a764_d92a7993a6d3_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-03T16:34:39.699195+00:00
-- url     : https://prove2.me/submissions/11e62796-47f7-4adf-a900-f0fdea318e4a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_e8818a47_c6bb_451e_9488_1f3faaa47e8f_a3
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_bound__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    L.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  obtain ⟨H, hH, hc, hm⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_e8818a47_c6bb_451e_9488_1f3faaa47e8f_a3 L hL hV
  have hb := WilliamsonShmoys.connected_planar_euler_bound__p2m_fa5d736f_5e40_4868_bcf6_007f98212d2a_a1 H hH hc hV
  exact le_trans (Nat.add_le_add_right hm 6) hb

