-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.bijunctive_algorithm_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:10:32.109722+00:00
-- url     : https://prove2.me/submissions/99dc0016-37d3-46df-8033-5d12359be7a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_output_law_exists
import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_output_approximates
import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_output_sensitivity
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution (Γ : Language) (rep : TwoCNFRepresentation Γ)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y z : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → z ∈ R.tuples →
      (fun i => (x i && y i) || (x i && z i) || (y i && z i)) ∈ R.tuples) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ A : Solver Γ, BijunctiveOutputLaw Γ rep ε A ∧ Approximates A ε ∧
        ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
          2 ≤ Fintype.card V →
          averageSensitivity A I ≤ C * ε⁻¹ * Real.log (Fintype.card V : ℝ) := by
  obtain ⟨C,hC,hSens⟩ := bijunctive_output_sensitivity Γ rep
  refine ⟨C,hC,?_⟩
  intro ε hε hε1
  obtain ⟨A,hLaw⟩ := bijunctive_output_law_exists Γ rep ε hε
  exact ⟨A,hLaw,bijunctive_output_approximates Γ rep ε hε hε1 A hLaw,
    hSens ε hε hε1 A hLaw⟩
