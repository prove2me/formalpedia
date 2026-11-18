-- Prove2me | solution 1 for StudentTeacher976.Adaptivity.auxiliary_student_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T03:56:03.684449+00:00
-- url     : https://prove2.me/submissions/d279723d-6f28-4c37-88c8-99c935f233c7

import Theorems.Thm_StudentTeacher976_Adaptivity_oracle_protocol_machine
import Theorems.Thm_StudentTeacher976_Adaptivity_auxiliary_student_protocol
set_option autoImplicit false
open QAdvFew.PoQOracle QAdvFew.PoQOracle.OTM.FiniteControl
open StudentTeacher976.Adaptivity

theorem solution (i : ℕ) (L : Language) (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (hr : AdmissibleRounds r) :
    UniformStudent i (auxiliaryStudent W r) := by
  obtain ⟨O, cpu, F, T, B, hO, hcpu, htrace, hspec⟩ := auxiliary_student_protocol i L W r hr
  obtain ⟨M, hM⟩ := oracle_protocol_machine cpu hcpu
  obtain ⟨clock, hrun⟩ := hM O F T B htrace
  refine ⟨F, ⟨O, M, clock, hO, ?_⟩, hspec⟩
  intro s
  refine ⟨?_, (hrun s).2⟩
  rw [(hrun s).1]
  rfl
