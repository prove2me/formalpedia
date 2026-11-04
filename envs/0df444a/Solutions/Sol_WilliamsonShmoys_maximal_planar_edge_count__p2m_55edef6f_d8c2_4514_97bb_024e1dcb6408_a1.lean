-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_55edef6f_d8c2_4514_97bb_024e1dcb6408_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:02:20.763633+00:00
-- url     : https://prove2.me/submissions/f9e95416-36af-41db-a2fa-c4811c3b4b16

import Theorems.Thm_WilliamsonShmoys_planar_edge_card_upper_bound__p2m_26140456_b7e4_4d83_b9c1_39ddc27ba139_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_card_lower_bound__p2m_26140456_b7e4_4d83_b9c1_39ddc27ba139_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N ≤ M) :
    M.edgeFinset.card = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_edge_card_upper_bound__p2m_26140456_b7e4_4d83_b9c1_39ddc27ba139_a1 M hM hcard
  · exact WilliamsonShmoys.maximal_planar_edge_card_lower_bound__p2m_26140456_b7e4_4d83_b9c1_39ddc27ba139_a1 M hM hcard hmax