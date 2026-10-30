-- Prove2me | solution 1 for WilliamsonShmoys.edgeFinset_card_lt_of_le_of_ne__p2m_2212fb5a_3b8b_4ff4_b66b_e1a858c8b349_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:10:55.005347+00:00
-- url     : https://prove2.me/submissions/bc359411-3716-4ddc-886a-320a1e11d50d

import Mathlib
open SimpleGraph

theorem solution {V : Type} (A B : SimpleGraph V) (hAfin : Fintype A.edgeSet)
    (hBfin : Fintype B.edgeSet) (hAB : A ≤ B) (hne : A ≠ B) :
    @Fintype.card A.edgeSet hAfin < @Fintype.card B.edgeSet hBfin := by
  letI : Fintype A.edgeSet := hAfin
  letI : Fintype B.edgeSet := hBfin
  exact Set.card_lt_card <| SimpleGraph.edgeSet_ssubset_edgeSet.mpr (lt_of_le_of_ne hAB hne)