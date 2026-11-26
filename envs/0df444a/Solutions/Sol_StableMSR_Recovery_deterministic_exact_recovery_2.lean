-- Prove2me | solution 2 for StableMSR.Recovery.deterministic_exact_recovery
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T01:45:04.286478+00:00
-- url     : https://prove2.me/submissions/ae8821cb-8891-48f6-aa00-60a9abbeb0d5

import Theorems.Thm_StableMSR_Recovery_exact_recovery_of_bounded_candidate_evaluation
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_bounded_tape_evaluation
import Definitions.Def_StableMSR_Recovery_Execution

set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery

/-- Theorem 1.1: finite programs precede all input data; every runtime is interpreter execution.
The parameter-envelope witness records the explicit bound of Appendix A.5. -/
theorem solution :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∃ C : ℝ, 0 < C ∧
      ∀ γ : ℝ, 1 < γ → ∃ ε₀ : ℚ, 0 < ε₀ ∧ ε₀ < 1 ∧
        (if γ < 2 then (γ - 1) / 2 ≤ (ε₀ : ℝ) ∧ (ε₀ : ℝ) < γ - 1
         else ε₀ = 1 / 2) ∧
        ((γ < 2 → (parameterEnvelope (ε₀ : ℝ) : ℝ) ≤ C / (γ - 1) ^ 5)) ∧
        ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
          ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
            1 ≤ k → k ≤ n → IsMetricArray d →
            RecoversWithin P n k d γ (a * n ^ (b * parameterEnvelope (ε₀ : ℝ))) := exact_recovery_of_bounded_candidate_evaluation StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.bounded_tape_evaluation


