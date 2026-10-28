-- Prove2me | solution 1 for TwoAgentSched.Shops.open_bjob_starts
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T05:52:52.583498+00:00
-- url     : https://prove2.me/submissions/fc98e869-bd24-4157-b36b-a48ef9c48bda

import Mathlib
import Definitions.Def_TwoAgentSched_Shops_Construction

open TwoAgentSched.Shops

theorem solution (p : List ℕ)
    (s₁ s₂ : Fin ((openInst p).nA + (openInst p).nB) → ℝ)
    (hfeas : IsOpenFeasible (openInst p).p1 (openInst p).p2 s₁ s₂)
    (hB : (openInst p).MeetsB s₁ s₂ (openQB p)) :
    (s₁ (openB p) = 0 ∧ s₂ (openB p) = partSum p / 2) ∨
      (s₂ (openB p) = 0 ∧ s₁ (openB p) = partSum p / 2) := by
  have hb : finSumFinEquiv.symm (openB p) = Sum.inr ⟨0, Nat.one_pos⟩ :=
    finSumFinEquiv_symm_apply_natAdd ⟨0, Nat.one_pos⟩
  have hp1 : (openInst p).p1 (openB p) = partSum p / 2 := by
    unfold Instance.p1
    rw [hb]
    rfl
  have hp2 : (openInst p).p2 (openB p) = partSum p / 2 := by
    unfold Instance.p2
    rw [hb]
    rfl
  have h1 : 0 ≤ s₁ (openB p) := hfeas.1 (openB p)
  have h2 : 0 ≤ s₂ (openB p) := hfeas.2.1 (openB p)
  obtain ⟨hB1, hB2⟩ := hB ⟨0, Nat.one_pos⟩
  change s₁ (openB p) + partSum p / 2 ≤ partSum p at hB1
  change s₂ (openB p) + partSum p / 2 ≤ partSum p at hB2
  rcases hfeas.2.2.2.2 (openB p) with h | h
  · rw [hp1] at h
    exact Or.inl ⟨by linarith, by linarith⟩
  · rw [hp2] at h
    exact Or.inr ⟨by linarith, by linarith⟩
