-- Prove2me | solution 1 for TwoAgentSched.deadline_exists
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T02:58:55.391854+00:00
-- url     : https://prove2.me/submissions/d31d42b8-b0b1-47f3-a3db-0b7a43f71539

import Mathlib
import Definitions.Def_TwoAgentSched_IsDeadline

open TwoAgentSched

namespace TwoAgentSched.DeadlineProof

lemma lex_true_true (t d : ℝ) :
    ((toLex (t, true) : ℝ ×ₗ Bool) : WithTop (ℝ ×ₗ Bool)) ≤
      ((toLex (d, true) : ℝ ×ₗ Bool) : WithTop (ℝ ×ₗ Bool)) ↔ t ≤ d := by
  rw [WithTop.coe_le_coe, Prod.Lex.toLex_le_toLex]
  simp only [Bool.le_refl, and_true]
  constructor
  · rintro (h | h)
    · exact le_of_lt h
    · exact h.le
  · exact lt_or_eq_of_le

lemma lex_true_false (t d : ℝ) :
    ((toLex (t, true) : ℝ ×ₗ Bool) : WithTop (ℝ ×ₗ Bool)) ≤
      ((toLex (d, false) : ℝ ×ₗ Bool) : WithTop (ℝ ×ₗ Bool)) ↔ t < d := by
  rw [WithTop.coe_le_coe, Prod.Lex.toLex_le_toLex]
  simp

lemma lex_true_top (t : ℝ) :
    ((toLex (t, true) : ℝ ×ₗ Bool) : WithTop (ℝ ×ₗ Bool)) ≤ ⊤ := le_top

theorem deadline_exists (f : ℝ → ℝ) (Q : ℝ) (hf : MonotoneOn f (Set.Ici 0)) :
    (∃ D : WithTop (ℝ ×ₗ Bool), IsDeadline f Q D) ∧
    ∀ d : ℝ, (∀ t, 0 ≤ t → t ≤ d → f t ≤ Q) → (∀ t, 0 ≤ t → d < t → Q < f t) →
      IsDeadline f Q ((toLex (d, true) : ℝ ×ₗ Bool) : WithTop (ℝ ×ₗ Bool)) := by
  constructor
  · let S : Set ℝ := {t | 0 ≤ t ∧ f t ≤ Q}
    by_cases hne : S.Nonempty
    · by_cases hbdd : BddAbove S
      · let d : ℝ := sSup S
        by_cases hdQ : f d ≤ Q
        · refine ⟨((toLex (d, true) : ℝ ×ₗ Bool) : WithTop (ℝ ×ₗ Bool)), ?_⟩
          intro t ht
          rw [lex_true_true]
          constructor
          · intro hft
            exact le_csSup hbdd (show t ∈ S from ⟨ht, hft⟩)
          · intro htd
            have hd0 : 0 ≤ d := by
              obtain ⟨s, hs⟩ := hne
              have hs' : 0 ≤ s ∧ f s ≤ Q := hs
              exact le_trans hs'.1 (le_csSup hbdd hs)
            exact le_trans (hf ht hd0 htd) hdQ
        · refine ⟨((toLex (d, false) : ℝ ×ₗ Bool) : WithTop (ℝ ×ₗ Bool)), ?_⟩
          intro t ht
          rw [lex_true_false]
          constructor
          · intro hft
            have htS : t ∈ S := ⟨ht, hft⟩
            have htd : t ≤ d := le_csSup hbdd htS
            rcases lt_or_eq_of_le htd with hlt | heq
            · exact hlt
            · exfalso
              exact hdQ (by rwa [heq] at hft)
          · intro hlt
            obtain ⟨s, hsS, hts⟩ := (lt_csSup_iff hbdd hne).mp hlt
            have hsS' : 0 ≤ s ∧ f s ≤ Q := hsS
            exact le_trans (hf ht hsS'.1 (le_of_lt hts)) hsS'.2
      · refine ⟨⊤, ?_⟩
        intro t ht
        constructor
        · intro _; exact le_top
        · intro _
          obtain ⟨s, hsS, hts⟩ := (not_bddAbove_iff.mp hbdd) t
          have hsS' : 0 ≤ s ∧ f s ≤ Q := hsS
          exact le_trans (hf ht hsS'.1 (le_of_lt hts)) hsS'.2
    · refine ⟨((toLex (0, false) : ℝ ×ₗ Bool) : WithTop (ℝ ×ₗ Bool)), ?_⟩
      intro t ht
      rw [lex_true_false]
      have hnot : ¬ f t ≤ Q := by
        intro hft
        exact hne ⟨t, ⟨ht, hft⟩⟩
      constructor
      · intro hft; exact absurd hft hnot
      · intro ht0; linarith
  · intro d hleft hright t ht
    rw [lex_true_true]
    constructor
    · intro hft
      by_contra htd
      have hdt : d < t := lt_of_not_ge htd
      have := hright t ht hdt
      linarith
    · intro htd
      exact hleft t ht htd

end TwoAgentSched.DeadlineProof

/-- Monotonicity turns every threshold `f t ≤ Q` into a cut of the deadline type. -/
theorem solution (f : ℝ → ℝ) (Q : ℝ) (hf : MonotoneOn f (Set.Ici 0)) :
    (∃ D : WithTop (ℝ ×ₗ Bool), IsDeadline f Q D) ∧
    ∀ d : ℝ, (∀ t, 0 ≤ t → t ≤ d → f t ≤ Q) → (∀ t, 0 ≤ t → d < t → Q < f t) →
      IsDeadline f Q ((toLex (d, true) : ℝ ×ₗ Bool) : WithTop (ℝ ×ₗ Bool)) :=
  TwoAgentSched.DeadlineProof.deadline_exists f Q hf
