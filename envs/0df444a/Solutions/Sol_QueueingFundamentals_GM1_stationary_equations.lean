-- Prove2me | solution 1 for QueueingFundamentals.GM1.stationary_equations
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:08:57.999119+00:00
-- url     : https://prove2.me/submissions/43064d8d-3cd3-4bb7-844a-18163820e733

import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain

open MeasureTheory in
theorem QueueingFundamentals.GM1.ba24aedd_column (A : Measure ℝ) (mu : ℝ) (q : ℕ → ℝ)
    (j : ℕ) (hj : 1 ≤ j) (x : ℝ) :
    HasSum (fun i => q i * QueueingFundamentals.GM1.transitionProb A mu i j) x ↔
      HasSum (fun k => q (j + k - 1) * QueueingFundamentals.GM1.serviceProb A mu k) x := by
  have hg : Function.Injective (fun k : ℕ => k + (j - 1)) := fun a b h => by
    simpa using h
  have hf : ∀ i, i ∉ Set.range (fun k : ℕ => k + (j - 1)) →
      q i * QueueingFundamentals.GM1.transitionProb A mu i j = 0 := by
    intro i hi
    have hlt : i < j - 1 := by
      by_contra hc
      exact hi ⟨i - (j - 1), by simp only; omega⟩
    have hj0 : j ≠ 0 := by omega
    have hji : ¬ j ≤ i + 1 := by omega
    simp [QueueingFundamentals.GM1.transitionProb, hj0, hji]
  rw [← hg.hasSum_iff hf]
  have hfun : ((fun i => q i * QueueingFundamentals.GM1.transitionProb A mu i j) ∘
      (fun k : ℕ => k + (j - 1))) =
      (fun k => q (j + k - 1) * QueueingFundamentals.GM1.serviceProb A mu k) := by
    funext k
    have hj0 : j ≠ 0 := by omega
    have hji : j ≤ k + (j - 1) + 1 := by omega
    have h1 : k + (j - 1) + 1 - j = k := by omega
    have h2 : k + (j - 1) = j + k - 1 := by omega
    show q (k + (j - 1)) * QueueingFundamentals.GM1.transitionProb A mu (k + (j - 1)) j = _
    rw [QueueingFundamentals.GM1.transitionProb, if_neg hj0, if_pos hji, h1, h2]
  rw [hfun]

open MeasureTheory QueueingFundamentals.GM1 in
theorem solution (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) (q : ℕ → ℝ) (hq0 : ∀ n, 0 ≤ q n) (hq1 : HasSum q 1) :
    (∀ j, HasSum (fun i => q i * transitionProb A mu i j) (q j)) ↔
      ((∀ i, 1 ≤ i → HasSum (fun k => q (i + k - 1) * serviceProb A mu k) (q i)) ∧
        HasSum (fun j => q j * (1 - ∑ k ∈ Finset.range (j + 1), serviceProb A mu k)) (q 0)) := by
  constructor
  · intro h
    refine ⟨fun i hi => (QueueingFundamentals.GM1.ba24aedd_column A mu q i hi (q i)).1 (h i), ?_⟩
    simpa [transitionProb] using h 0
  · rintro ⟨h1, h0⟩ j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simpa [transitionProb] using h0
    · exact (QueueingFundamentals.GM1.ba24aedd_column A mu q j hj (q j)).2 (h1 j hj)
