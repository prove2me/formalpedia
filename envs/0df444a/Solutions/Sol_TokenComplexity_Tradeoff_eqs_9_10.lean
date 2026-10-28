-- Prove2me | solution 1 for TokenComplexity.Tradeoff.eqs_9_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:42:52.831546+00:00
-- url     : https://prove2.me/submissions/915fc9cc-b000-4c98-855a-ca2abd55cf4d

import Mathlib
import Definitions.Def_TokenComplexity_Tradeoff_Model

open Finset

open TokenComplexity.Tradeoff in
theorem solution {n : ℕ} {Prompt : Type} (B : Benchmark n Prompt) (τ : Fin n → ℕ∞)
    (hA1 : TokenComplexityHyp B τ) (hRich : Rich B) :
    (∀ T v : ℝ, IsOptAccuracy B T v ↔
      IsGreatest {a | ∃ t : Fin n → ℕ, (∑ i, (t i : ℝ)) / n ≤ T ∧
        a = ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n} v) ∧
    (∀ α v : ℝ, IsMinAvgLen B α v ↔
      IsLeast {L | ∃ t : Fin n → ℕ,
        α ≤ ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n ∧
        L = (∑ i, (t i : ℝ)) / n} v) := by
  have hacc : ∀ P, accuracy B P
      = ((univ.filter (fun i => τ i ≤ (B.len P i : ℕ∞))).card : ℝ) / n := by
    intro P
    unfold accuracy
    rw [Finset.filter_congr (fun i _ => hA1 P i)]
  have hlen : ∀ P, avgLen B P = (∑ i, (B.len P i : ℝ)) / n := fun P => rfl
  refine ⟨fun T v => ?_, fun α v => ?_⟩
  · unfold IsOptAccuracy
    have hS : {a | ∃ P, avgLen B P ≤ T ∧ accuracy B P = a}
        = {a | ∃ t : Fin n → ℕ, (∑ i, (t i : ℝ)) / n ≤ T ∧
          a = ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n} := by
      ext a
      constructor
      · rintro ⟨P, h1, h2⟩
        exact ⟨B.len P, by rw [← hlen]; exact h1, by rw [← h2, hacc]⟩
      · rintro ⟨t, h1, h2⟩
        obtain ⟨P, hP⟩ := hRich t
        have ht : B.len P = t := funext hP
        subst ht
        exact ⟨P, by rw [hlen]; exact h1, by rw [h2, hacc]⟩
    rw [hS]
  · unfold IsMinAvgLen
    have hS : {L | ∃ P, α ≤ accuracy B P ∧ avgLen B P = L}
        = {L | ∃ t : Fin n → ℕ,
          α ≤ ((univ.filter (fun i => τ i ≤ (t i : ℕ∞))).card : ℝ) / n ∧
          L = (∑ i, (t i : ℝ)) / n} := by
      ext L
      constructor
      · rintro ⟨P, h1, h2⟩
        exact ⟨B.len P, by rw [← hacc]; exact h1, by rw [← h2, hlen]⟩
      · rintro ⟨t, h1, h2⟩
        obtain ⟨P, hP⟩ := hRich t
        have ht : B.len P = t := funext hP
        subst ht
        exact ⟨P, by rw [hacc]; exact h1, by rw [h2, hlen]⟩
    rw [hS]
