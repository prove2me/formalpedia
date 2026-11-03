-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_f8b110d8_67db_4582_b9bf_9e52697d207d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:13:18.770501+00:00
-- url     : https://prove2.me/submissions/51512184-cd1c-44b4-b8c3-7ac0ee99fd0e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_e087affc_3721_47e3_9583_19a35624e79d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_e087affc_3721_47e3_9583_19a35624e79d_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V) (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S) :
    letI : DecidableRel S.Adj := Classical.decRel S.Adj
    S.edgeFinset.card + 6 = 3 * Fintype.card V := by
  letI : DecidableRel S.Adj := Classical.decRel S.Adj
  have hupper := WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_e087affc_3721_47e3_9583_19a35624e79d_a1 S hS hcard
  have hlower := WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_e087affc_3721_47e3_9583_19a35624e79d_a1 S hS hcard hmax
  omega
