-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_eq__p2m_3ab951ac_7c5a_45ca_9684_f3fed84a5e33_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:12:47.948212+00:00
-- url     : https://prove2.me/submissions/bb7f930e-2174-4226-8e6f-d919cddb02f8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_1d31a56b_8574_4be9_a710_fc2e7a582d14_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_1d31a56b_8574_4be9_a710_fc2e7a582d14_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_edge_count_upper__p2m_1d31a56b_8574_4be9_a710_fc2e7a582d14_a1 K hcard hK
  · exact WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_1d31a56b_8574_4be9_a710_fc2e7a582d14_a1 K hcard hK hmax