-- Prove2me | solution 1 for PrivateAgnosticHalfspace.Gaussian.ordered_regression_programs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:03:50.914045+00:00
-- url     : https://prove2.me/submissions/6881fefc-c65b-481f-b0de-de396f42ddd2

import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_ordered_optimizer_program
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_ordered_learner_program
import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_OptimizerRealization
open MeasureTheory ProbabilityTheory
set_option autoImplicit false
open PrivateAgnosticHalfspace.Gaussian

theorem solution :
    ∃ optimizerCode learnerCode : LearnerProgram,
    ∀ O : Optimizer, RealizesOrderedRegression O →
      (∀ d p n : ℕ, 1 ≤ p → 2 ≤ n → ∀ ε δ : ℝ,
        0 < ε ∧ ε ≤ 1/2 → 0 < δ ∧ δ ≤ 1/2 →
        ∀ S : Fin n → Example d, ∃ fuel cost : ℕ,
          (cost : ℝ) ≤ (100000 : ℝ)*((n : ℝ)*p*featureDimension d p+n^2*featureDimension d p) ∧
          Implements optimizerCode fuel cost d p 1 (optimizerInput d p n ε δ S)
            ((O d p n ε δ S : Measure (UnitBall d p)).map (fun v => (v,(0 : Fin 1))))) ∧
      (∀ d p k M n₀ m : ℕ, 1 ≤ p → 0 < k → 0 < M → 0 < m →
        featureDimension d p ≤ n₀ → m ≤ k*n₀ → p ≤ featureDimension d p → M ≤ p →
        ∀ ε δ α β : ℝ, 0 < ε ∧ ε ≤ 1/2 → 0 < δ ∧ δ ≤ 1/2 →
        ∀ S : Fin (k*n₀+m) → Example d, ∃ fuel cost : ℕ,
          (cost : ℝ) ≤ (100000 : ℝ)*(((k*n₀+m : ℕ) : ℝ)*p*featureDimension d p+
            (k : ℝ)*n₀^2*featureDimension d p+(k : ℝ)*M*m*featureDimension d p) ∧
          (cost : ℝ) ≤ 3*(100000 : ℝ)*((k*n₀+m : ℕ) : ℝ)^3 ∧
          Implements learnerCode fuel cost d p M (learnerInput d p k M n₀ m ε δ α β S)
            (algorithmLaw O d p k M n₀ m ε δ S)) := by
  obtain ⟨optimizerCode,hOpt⟩ := ordered_optimizer_program
  obtain ⟨learnerCode,hLearn⟩ := ordered_learner_program
  refine ⟨optimizerCode,learnerCode,?_⟩
  intro O hO
  exact ⟨hOpt O hO,hLearn O hO⟩
