-- Prove2me | solution 3 for StableMSR.Recovery.deterministic_exact_recovery
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T02:45:27.659988+00:00
-- url     : https://prove2.me/submissions/a32bbd83-67ac-4c9b-ac33-def51da290ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StableMSR_Recovery_exact_recovery_of_initialized_separator_traversal
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_bounded_initialized_traversal
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
            RecoversWithin P n k d γ (a * n ^ (b * parameterEnvelope (ε₀ : ℝ))) := StableMSR.Recovery.exact_recovery_of_initialized_separator_traversal StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.bounded_initialized_traversal


