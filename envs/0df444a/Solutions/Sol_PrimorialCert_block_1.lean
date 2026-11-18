-- Prove2me | solution 1 for PrimorialCert.block_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:27:54.709819+00:00
-- url     : https://prove2.me/submissions/22c8bd87-6c32-4b9f-8d71-54c6515d2eb2

import Definitions.Def_PrimorialCertData_1

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData1.q0 : PrimData1.s0.bok = true := by decide +kernel
theorem PrimData1.q1 : PrimData1.s1.bok = true := by decide +kernel
theorem PrimData1.q2 : PrimData1.s2.bok = true := by decide +kernel
theorem PrimData1.q3 : PrimData1.s3.bok = true := by decide +kernel
theorem PrimData1.q4 : PrimData1.s4.bok = true := by decide +kernel
theorem PrimData1.q5 : PrimData1.s5.bok = true := by decide +kernel
theorem PrimData1.q6 : PrimData1.s6.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData1.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData1.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData1.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData1.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData1.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData1.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData1.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData1.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData1.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData1.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData1.q6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
