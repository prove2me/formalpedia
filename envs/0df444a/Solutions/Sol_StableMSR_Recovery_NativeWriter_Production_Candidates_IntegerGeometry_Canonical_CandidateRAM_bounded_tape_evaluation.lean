-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.bounded_tape_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T02:21:26.319592+00:00
-- url     : https://prove2.me/submissions/76a6a449-8a8c-46f9-b3df-8424615f5fa9

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_source_emission_realized
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_bounded_stream_evaluation
import Definitions.Def_StableMSR_LogicalCandidateProgram
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
  ∃F t,F≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    CandidateRAM.run F [CandidateRAM.code (budget (e:ℝ)) (widthBound (e:ℝ))] (CandidateRAM.banks s)=some t ∧
    (∀q:ℤ,(∀i:ℕ,q≠cell 5 i ∧ q≠cell 7 i) → t.mem q=s.imem q) ∧
    Candidates.Input x.n t.mem (tape CandidateRAM.Naming.name (Canonical.integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ))) := by
  obtain ⟨c,D,b,alg⟩:=Logical.bounded_stream_evaluation
  refine ⟨c,D,b,?_⟩
  intro e ep el x s k1 kn ready mat r p rr rp hr he
  obtain ⟨t,z,ex,tm,closed,stream⟩:=alg e ep el x s k1 kn ready mat r p rr rp hr he
  obtain ⟨k,u,hk,run,frame,correct⟩:=Logical.source_emission_realized x.n _ _ (CandidateRAM.banks s) t z ex closed
  rw [stream] at correct
  exact ⟨k,u,hk.trans tm,run,frame,correct⟩