-- Prove2me | solution 1 for PrimorialCert.block_14
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-17T22:28:20.719063+00:00
-- url     : https://prove2.me/submissions/e62cb8c6-6f7f-46fa-a0de-eca47f746052

import Definitions.Def_PrimorialCertData_14

namespace ThetaSieve
set_option maxHeartbeats 0

theorem PrimData14.q0 : PrimData14.s0.bok = true := by decide +kernel
theorem PrimData14.q1 : PrimData14.s1.bok = true := by decide +kernel
theorem PrimData14.q2 : PrimData14.s2.bok = true := by decide +kernel
theorem PrimData14.q3 : PrimData14.s3.bok = true := by decide +kernel
theorem PrimData14.q4 : PrimData14.s4.bok = true := by decide +kernel
theorem PrimData14.q5 : PrimData14.s5.bok = true := by decide +kernel
theorem PrimData14.q6 : PrimData14.s6.bok = true := by decide +kernel

end ThetaSieve

set_option maxHeartbeats 0 in
theorem solution :
    (∀ s ∈ ThetaSieve.PrimData14.segs, s.bok = true) ∧ ThetaSieve.chainOK ThetaSieve.PrimData14.segs = true ∧
    (∀ s ∈ ThetaSieve.PrimData14.segs, 16000001 < s.L + 2 * s.W → s.hi' < (s.L - 1) * 18458400208034708012) :=
  ⟨by unfold ThetaSieve.PrimData14.segs; exact List.forall_mem_cons.2 ⟨ThetaSieve.PrimData14.q0, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData14.q1, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData14.q2, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData14.q3, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData14.q4, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData14.q5, List.forall_mem_cons.2 ⟨ThetaSieve.PrimData14.q6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩,
   by decide +kernel, by decide +kernel⟩
