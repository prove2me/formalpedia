-- Prove2me | solution 1 for StableMSR.Recovery.exact_recovery_of_initialized_separator_traversal
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T02:39:14.031529+00:00
-- url     : https://prove2.me/submissions/8c7f8c1a-9d71-4b99-95d7-c87b07de991d

import Theorems.Thm_StableMSR_Recovery_exact_recovery_of_bounded_candidate_evaluation
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_bounded_stream_of_initialized_traversal
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_source_emission_realized
import Definitions.Def_StableMSR_InitializedSeparatorTraversal
import Definitions.Def_StableMSR_Recovery_Execution
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
theorem solution (traversal:Logical.MiddleCorrect) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∃ C : ℝ, 0 < C ∧
      ∀ γ : ℝ, 1 < γ → ∃ ε₀ : ℚ, 0 < ε₀ ∧ ε₀ < 1 ∧
        (if γ < 2 then (γ - 1) / 2 ≤ (ε₀ : ℝ) ∧ (ε₀ : ℝ) < γ - 1
         else ε₀ = 1 / 2) ∧
        ((γ < 2 → (parameterEnvelope (ε₀ : ℝ) : ℝ) ≤ C / (γ - 1) ^ 5)) ∧
        ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
          ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
            1 ≤ k → k ≤ n → IsMetricArray d →
            RecoversWithin P n k d γ (a * n ^ (b * parameterEnvelope (ε₀ : ℝ))) := by
  apply StableMSR.Recovery.exact_recovery_of_bounded_candidate_evaluation
  obtain ⟨c,D,b,exec⟩:=Logical.bounded_stream_of_initialized_traversal traversal
  refine ⟨c,D,b,?_⟩
  intro e ep el x s hk kn rd bounded r p rr rp live used
  obtain ⟨t,z,ex,tm,cl,records⟩:=exec e ep el x s hk kn rd bounded r p rr rp live used
  obtain ⟨k,u,le,run,frame,words⟩:=Logical.source_emission_realized x.n _ _ (CandidateRAM.banks s) t z ex cl
  rw [records] at words
  exact ⟨k,u,le.trans tm,run,frame,words⟩
