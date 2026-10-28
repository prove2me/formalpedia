-- Prove2me | solution 1 for WilliamsonShmoys.finite_edge_augmentation_completion__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:36:17.338135+00:00
-- url     : https://prove2.me/submissions/85a8699c-0443-479f-af68-fcb99b779a09

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V)
    (m : ℕ)
    (hP : P G)
    (hBound : G.edgeSet.ncard ≤ m)
    (hAugment : ∀ K : SimpleGraph V, P K → K.edgeSet.ncard < m →
      ∃ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet ∧
        L.edgeSet.ncard = K.edgeSet.ncard + 1 ∧
        P L) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      H.edgeSet.ncard = m ∧
      P H := by
  classical
  have aux : ∀ d : ℕ, ∀ K : SimpleGraph V, P K → K.edgeSet.ncard ≤ m →
      m - K.edgeSet.ncard = d →
      ∃ H : SimpleGraph V,
        K.edgeSet ⊆ H.edgeSet ∧ H.edgeSet.ncard = m ∧ P H := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro K hPK hKBound hGap
        by_cases hEq : K.edgeSet.ncard = m
        · exact ⟨K, Set.Subset.rfl, hEq, hPK⟩
        · have hLt : K.edgeSet.ncard < m := by omega
          obtain ⟨L, hKL, hCard, hPL⟩ := hAugment K hPK hLt
          have hLBound : L.edgeSet.ncard ≤ m := by omega
          have hGapL : m - L.edgeSet.ncard < d := by
            rw [hCard]
            omega
          obtain ⟨H, hLH, hHCard, hPH⟩ :=
            ih (m - L.edgeSet.ncard) hGapL L hPL hLBound rfl
          exact ⟨H, hKL.trans hLH, hHCard, hPH⟩
  exact aux (m - G.edgeSet.ncard) G hP hBound rfl