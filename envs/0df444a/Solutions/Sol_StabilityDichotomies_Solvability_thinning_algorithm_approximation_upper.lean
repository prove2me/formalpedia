-- Prove2me | solution 1 for StabilityDichotomies.Solvability.thinning_algorithm_approximation_upper
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:54:12.333996+00:00
-- url     : https://prove2.me/submissions/d141bfdf-ae98-4757-adb1-e3529206aae5

import Theorems.Thm_StabilityDichotomies_Solvability_thinning_law_and_sensitivity
import Theorems.Thm_StabilityDichotomies_Solvability_thinning_output_approximates
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability

theorem solution (Γ : Language) (b : Bool)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples →
      (fun i => if b then x i || y i else x i && y i) ∈ R.tuples) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ A : Solver Γ, ThinningOutputLaw Γ b ε A ∧ Approximates A ε ∧
        ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
          averageSensitivity A I ≤ C * ε⁻¹ := by
  obtain ⟨C,hC,h⟩ := thinning_law_and_sensitivity Γ b hΓ
  refine ⟨C,hC,?_⟩
  intro ε hε hε1
  obtain ⟨A,hLaw,hSens⟩ := h ε hε hε1
  exact ⟨A,hLaw,thinning_output_approximates Γ b hΓ ε hε hε1 A hLaw,hSens⟩
