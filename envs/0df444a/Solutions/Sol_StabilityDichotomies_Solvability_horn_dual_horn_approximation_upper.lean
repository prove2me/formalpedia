-- Prove2me | solution 1 for StabilityDichotomies.Solvability.horn_dual_horn_approximation_upper
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:35:08.022195+00:00
-- url     : https://prove2.me/submissions/d45a25b0-21ab-42fa-9021-2c3ff2a99c94

import Theorems.Thm_StabilityDichotomies_Solvability_thinning_algorithm_approximation_upper
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability

theorem solution (Γ : Language)
    (hΓ : (∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → (fun i => x i && y i) ∈ R.tuples) ∨
      (∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → (fun i => x i || y i) ∈ R.tuples)) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ A : Solver Γ, Approximates A ε ∧
        ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
          averageSensitivity A I ≤ C * ε⁻¹ := by
  obtain ⟨b, hb⟩ : ∃ b : Bool, ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples →
      (fun i => if b then x i || y i else x i && y i) ∈ R.tuples := by
    rcases hΓ with h | h
    · exact ⟨false, by simpa using h⟩
    · exact ⟨true, by simpa using h⟩
  obtain ⟨C, hC, hbound⟩ := thinning_algorithm_approximation_upper Γ b hb
  refine ⟨C, hC, ?_⟩
  intro ε hε hε1
  obtain ⟨A, hLaw, hApprox, hSens⟩ := hbound ε hε hε1
  exact ⟨A, hApprox, hSens⟩
