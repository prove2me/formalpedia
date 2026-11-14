-- Prove2me | solution 1 for StabilityDichotomies.Solvability.bijunctive_approximation_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:51:42.115204+00:00
-- url     : https://prove2.me/submissions/81bab1e6-e098-4ebb-a78a-bf97c60ffcb7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_has_two_cnf_representation
import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_algorithm_upper
noncomputable section
open scoped Classical
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution (Γ : Language)
    (hΓ : ∀ R ∈ Γ.relations, ∀ x y z : Fin R.arity → Bool,
      x ∈ R.tuples → y ∈ R.tuples → z ∈ R.tuples →
      (fun i => (x i && y i) || (x i && z i) || (y i && z i)) ∈ R.tuples) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ A : Solver Γ, Approximates A ε ∧
        ∀ (V : Type) [Fintype V] (I : Instance Γ V), Satisfiable I →
          2 ≤ Fintype.card V →
          averageSensitivity A I ≤ C * ε⁻¹ * Real.log (Fintype.card V : ℝ) := by
  obtain ⟨rep⟩ := bijunctive_has_two_cnf_representation Γ hΓ
  obtain ⟨C,hC,h⟩ := bijunctive_algorithm_upper Γ rep hΓ
  refine ⟨C,hC,?_⟩
  intro ε hε hε1
  obtain ⟨A,hLaw,hApprox,hSens⟩ := h ε hε hε1
  exact ⟨A,hApprox,hSens⟩
