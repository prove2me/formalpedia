-- Prove2me | solution 1 for StudentTeacher976.Adaptivity.auxiliary_test_efficient
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T03:55:30.772533+00:00
-- url     : https://prove2.me/submissions/3814bd0a-5ecf-479a-b793-744ede59c017

import Theorems.Thm_StudentTeacher976_Adaptivity_oracle_protocol_machine
import Theorems.Thm_StudentTeacher976_Adaptivity_auxiliary_test_protocol
set_option autoImplicit false
open QAdvFew.PoQOracle QAdvFew.PoQOracle.OTM.FiniteControl
open StudentTeacher976.Adaptivity

theorem solution (i : ℕ) (L : Language) (W : WitnessPresentation i L)
    (r : ℕ → ℕ) (hr : AdmissibleRounds r) :
    {s | ∃ x y z, s = QAdvFew.PoQOracle.tup [x, y, z] ∧ auxiliaryTest W r x y z} ∈ Delta i := by
  obtain ⟨O, cpu, F, T, B, hO, hcpu, htrace, hspec⟩ := auxiliary_test_protocol i L W r hr
  obtain ⟨M, hM⟩ := oracle_protocol_machine cpu hcpu
  obtain ⟨clock, hrun⟩ := hM O F T B htrace
  refine ⟨O, M, clock, hO, ?_, ?_⟩
  · intro s
    rw [(hrun s).1]
    rfl
  · intro s
    rw [(hrun s).1]
    simpa only [Option.some.injEq, Set.mem_setOf_eq] using (hspec s).symm
