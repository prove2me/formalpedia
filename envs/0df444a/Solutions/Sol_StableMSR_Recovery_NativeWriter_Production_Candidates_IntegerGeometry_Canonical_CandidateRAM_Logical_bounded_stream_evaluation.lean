-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.bounded_stream_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T02:39:36.813475+00:00
-- url     : https://prove2.me/submissions/fba77849-ab4a-483f-8073-559f315a718a

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_bounded_stream_of_initialized_traversal
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_bounded_initialized_traversal
import Definitions.Def_StableMSR_InitializedSeparatorTraversal
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
theorem solution :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃t z,Logical.Executes x.n s.imem (Logical.candidate (budget (e:ℝ)) (widthBound (e:ℝ)))
       (Logical.initial (CandidateRAM.banks s)) t z ∧ z ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
       t.closed=true ∧ t.output=tape CandidateRAM.Naming.name
         (Canonical.integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ)) := Logical.bounded_stream_of_initialized_traversal Logical.bounded_initialized_traversal