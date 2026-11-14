-- Prove2me | solution 1 for StabilityDichotomies.Solvability.thinning_law_and_sensitivity
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:58:10.673933+00:00
-- url     : https://prove2.me/submissions/5940511e-bafe-4dc3-834a-095fbf10cde3

import Theorems.Thm_StabilityDichotomies_Solvability_thinning_output_law_exists
import Theorems.Thm_StabilityDichotomies_Solvability_thinning_output_sensitivity
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability

theorem solution (Γ : Language) (b : Bool)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples →
      (fun i => if b then x i || y i else x i && y i) ∈ R.tuples) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ A : Solver Γ, ThinningOutputLaw Γ b ε A ∧
        ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
          averageSensitivity A I ≤ C * ε⁻¹ := by
  obtain ⟨C,hC,h⟩ := thinning_output_sensitivity Γ b hΓ
  refine ⟨C,hC,?_⟩
  intro ε hε hε1
  obtain ⟨A,hA⟩ := thinning_output_law_exists Γ b ε hε hε1
  exact ⟨A,hA,h ε hε hε1 A hA⟩
