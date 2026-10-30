-- Prove2me | solution 1 for WilliamsonShmoys.connected_spanning_tree_card__p2m_1954d530_c7a1_4324_8033_8836e3ec1363_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:43:05.325247+00:00
-- url     : https://prove2.me/submissions/6cdbbe8e-5884-475c-be2b-78ccd8a99ca0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hconnected : H.Connected) :
    (Fintype.card V = 0 ∧ H.edgeSet.ncard = 0) ∨
      ∃ T : SimpleGraph V, T ≤ H ∧ T.Connected ∧
        T.edgeSet.ncard + 1 = Fintype.card V := by
  classical
  by_cases hV : Nonempty V
  · obtain ⟨T, hTH, hTtree⟩ := hconnected.exists_isTree_le
    right
    refine ⟨T, hTH, hTtree.connected, ?_⟩
    rw [← Set.fintypeCard_eq_ncard, ← T.edgeFinset_card]
    exact hTtree.card_edgeFinset
  · left
    haveI : IsEmpty V := not_nonempty_iff.mp hV
    have hVcard : Fintype.card V = 0 := Fintype.card_eq_zero_iff.mpr ‹IsEmpty V›
    have hEempty : IsEmpty H.edgeSet := inferInstance
    have hEcard : Fintype.card H.edgeSet = 0 :=
      Fintype.card_eq_zero_iff.mpr hEempty
    constructor
    · exact hVcard
    · rw [← Set.fintypeCard_eq_ncard]
      exact hEcard