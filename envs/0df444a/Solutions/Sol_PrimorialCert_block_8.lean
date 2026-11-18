-- Prove2me | solution 1 for PrimorialCert.block_8
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:08.714715+00:00
-- url     : https://prove2.me/submissions/f598041b-61a7-4d8f-a96f-50420de52c68

import Definitions.Def_PrimorialCertData_8

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData8.q0 : PrimData8.s0.bok = true := by decide +kernel
theorem PrimData8.q1 : PrimData8.s1.bok = true := by decide +kernel
theorem PrimData8.q2 : PrimData8.s2.bok = true := by decide +kernel
theorem PrimData8.q3 : PrimData8.s3.bok = true := by decide +kernel
theorem PrimData8.q4 : PrimData8.s4.bok = true := by decide +kernel
theorem PrimData8.q5 : PrimData8.s5.bok = true := by decide +kernel
theorem PrimData8.q6 : PrimData8.s6.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData8.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData8.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData8.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData8.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData8.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData8.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData8.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData8.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData8.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData8.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData8.q6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
