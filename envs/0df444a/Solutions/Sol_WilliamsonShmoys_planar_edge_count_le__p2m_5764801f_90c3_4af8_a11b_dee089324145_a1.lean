-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_le__p2m_5764801f_90c3_4af8_a11b_dee089324145_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:22:17.117055+00:00
-- url     : https://prove2.me/submissions/47803c46-5823-48ad-9e3c-aba40ed85055

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_of_card_ge_three__p2m_511609d8_7f6a_4ba7_bd36_d7671338159d_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_small_card__p2m_511609d8_7f6a_4ba7_bd36_d7671338159d_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeFinset.card ≤
      (if Fintype.card V < 3 then (Fintype.card V).choose 2
       else 3 * Fintype.card V - 6) := by
  by_cases hsmall : Fintype.card V < 3
  · simpa [hsmall] using
      (WilliamsonShmoys.planar_edge_bound_small_card__p2m_511609d8_7f6a_4ba7_bd36_d7671338159d_a1
        L dL hsmall)
  · have hlarge : 3 ≤ Fintype.card V := Nat.le_of_not_gt hsmall
    simpa [hsmall] using
      (WilliamsonShmoys.planar_drawing_edge_bound_of_card_ge_three__p2m_511609d8_7f6a_4ba7_bd36_d7671338159d_a1
        L dL hL hlarge)