-- Prove2me | solution 1 for PrimorialCert.block_12
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:16.795864+00:00
-- url     : https://prove2.me/submissions/1f856015-28bb-4f35-b9df-c3316eadb9f2

import Definitions.Def_PrimorialCertData_12

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData12.q0 : PrimData12.s0.bok = true := by decide +kernel
theorem PrimData12.q1 : PrimData12.s1.bok = true := by decide +kernel
theorem PrimData12.q2 : PrimData12.s2.bok = true := by decide +kernel
theorem PrimData12.q3 : PrimData12.s3.bok = true := by decide +kernel
theorem PrimData12.q4 : PrimData12.s4.bok = true := by decide +kernel
theorem PrimData12.q5 : PrimData12.s5.bok = true := by decide +kernel
theorem PrimData12.q6 : PrimData12.s6.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData12.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData12.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData12.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData12.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData12.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData12.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData12.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData12.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData12.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData12.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData12.q6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
